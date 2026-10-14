import Erdos821.P8.DensityPerturbation

noncomputable section
open scoped BigOperators

namespace Erdos821.P8Core
open Blueprint

/-- On the compact parameter region, its outer cutoff includes every nonzero term. -/
theorem densityRemainder_eq_sum_on_region {b wMax gamma w : ℝ} {K : ℕ}
    (hb : 0 < b) (hbg : b ≤ gamma) (hgw : gamma ≤ w) (hww : w ≤ wMax)
    (hK : ⌊wMax / b⌋₊ ≤ K) :
    densityRemainder gamma w =
      ∑ l ∈ Finset.Icc 2 K, densityTerm gamma w l / (l.factorial : ℝ) := by
  have hgamma : 0 < gamma := hb.trans_le hbg
  have hmax : 0 ≤ wMax := (hgamma.le.trans hgw).trans hww
  have hratio : w / gamma ≤ wMax / b := by
    calc
      w / gamma ≤ wMax / gamma := div_le_div_of_nonneg_right hww hgamma.le
      _ ≤ wMax / b := div_le_div_of_nonneg_left hmax hb hbg
  have hfloor : ⌊w / gamma⌋₊ ≤ K := (Nat.floor_mono hratio).trans hK
  rw [densityRemainder, roughDensity_eq_cutoff gamma w hgamma K hfloor,
    add_sub_cancel_left]

/-- The finite target in the grid task absorbs parameter and multiplicative losses. -/
theorem densityTerm_sum_weighted_perturbation_on_region {b wMax gap eps : ℝ}
    (hb : 0 < b) (hgap : 0 < gap) (heps : 0 < eps) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ gamma w gamma' w' a : ℝ, ∀ K : ℕ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax → ⌊wMax / b⌋₊ ≤ K →
      |gamma' - gamma| < rho → |w' - w| < rho → 0 ≤ a → a < rho →
      (1 + a) * (∑ l ∈ Finset.Icc 2 K,
        densityTerm gamma' w' l / (l.factorial : ℝ)) ≤
        (∑ l ∈ Finset.Icc 2 K, densityTerm gamma w l / (l.factorial : ℝ)) + eps := by
  obtain ⟨rho, hrho, hmod⟩ := densityTerm_sum_weighted_perturbation
    (wMax := wMax) hb hgap heps
  refine ⟨rho, hrho, ?_⟩
  intro gamma w gamma' w' a K hbg hgw hww hK hg hw ha harho
  have h := hmod gamma w gamma' w' a K hbg hgw hww hg hw ha harho
  change _ ≤ densityRemainder gamma w + eps at h
  rw [densityRemainder_eq_sum_on_region hb hbg (by linarith) hww hK] at h
  exact h

/-- One uniform radius also absorbs the additive errors from a finite grid. -/
theorem densityTerm_sum_grid_errors {b wMax gap eps : ℝ}
    (hb : 0 < b) (hgap : 0 < gap) (heps : 0 < eps) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ gamma w gamma' w' a E : ℝ, ∀ K : ℕ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax → ⌊wMax / b⌋₊ ≤ K →
      |gamma' - gamma| < rho → |w' - w| < rho → 0 ≤ a → a < rho → E < rho →
      (1 + a) * (∑ l ∈ Finset.Icc 2 K,
        densityTerm gamma' w' l / (l.factorial : ℝ)) + E ≤
        (∑ l ∈ Finset.Icc 2 K, densityTerm gamma w l / (l.factorial : ℝ)) + eps := by
  obtain ⟨rho, hrho, hmod⟩ := densityTerm_sum_weighted_perturbation_on_region
    (wMax := wMax) hb hgap (show 0 < eps / 2 by positivity)
  refine ⟨min rho (eps / 2), lt_min hrho (by positivity), ?_⟩
  intro gamma w gamma' w' a E K hbg hgw hww hK hg hw ha harho hE
  have h := hmod gamma w gamma' w' a K hbg hgw hww hK
    (hg.trans_le (min_le_left _ _)) (hw.trans_le (min_le_left _ _)) ha
    (harho.trans_le (min_le_left _ _))
  have hE' : E < eps / 2 := hE.trans_le (min_le_right _ _)
  linarith

end Erdos821.P8Core

