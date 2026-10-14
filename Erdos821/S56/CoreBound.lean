import Erdos821.S56.Separated
import Erdos821.S56.GroupParts
import Erdos821.S56.Rankin

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem norm_mellin (n sigma : ℝ) : ‖mellin n sigma‖ = 1 := by
  unfold Erdos821.Blueprint.Analytic.mellin
  simp [Complex.norm_exp]

theorem card_divisors_antidiagonal (t : ℕ) : t.divisorsAntidiagonal.card = t.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

theorem roughCore_norm_bound (x lo hi sigma M : ℝ) (c : ℕ → ℂ) (hM : 0 ≤ M)
    (hc : ∀ r, ‖c r‖ ≤ M) (t : ℕ) :
    ‖roughCore x lo hi sigma c t‖ ≤ (t.divisors.card : ℝ) * M := by
  unfold roughCore
  calc
    _ ≤ ∑ pr ∈ t.divisorsAntidiagonal,
        ‖if lo ≤ (pr.1 : ℝ) ∧ (pr.1 : ℝ) ≤ hi ∧ rough (W x) pr.1 then
          mellin pr.1 sigma * c pr.2 else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _pr ∈ t.divisorsAntidiagonal, M := by
      apply Finset.sum_le_sum
      intro pr _
      split_ifs
      · simpa only [norm_mul, norm_mellin, one_mul] using hc pr.2
      · simpa only [norm_zero] using hM
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, card_divisors_antidiagonal]

theorem hCoefficient_norm_bound (P : Geometry) (G : PrimeGroups)
    (x lo hi rho sigma M R : ℝ) (c : ℕ → ℂ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hc : ∀ r, ‖c r‖ ≤ M)
    (hw : ∀ h, markWeight G P.q (fun _ => P.ell) h ≤ R)
    (h : ℕ) (hh : 0 < h) :
    ‖hCoefficient P G x lo hi rho sigma c h‖ ≤ R * M * (h.divisors.card : ℝ) := by
  have hmark0 := markWeight_nonneg G P.q P.damping.1.le (fun _ => P.ell) h
  have hcard : ((groupFreePart G h).divisors.card : ℝ) ≤ h.divisors.card := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hh.ne' (groupFreePart_dvd G h hh))
  simp only [hCoefficient, norm_mul, norm_mellin, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmark0]
  calc
    _ ≤ R * (((groupFreePart G h).divisors.card : ℝ) * M) :=
      mul_le_mul (hw h) (roughCore_norm_bound x lo hi sigma M c hM hc _)
        (norm_nonneg _) hR
    _ ≤ R * M * (h.divisors.card : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hcard (mul_nonneg hR hM)
      simpa [mul_assoc, mul_comm, mul_left_comm] using h


end Erdos821.S56Core
