import Erdos821.P7.HarmonicPLower
import Erdos821.S56.TailSaving

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem tsum_head_add_tail (f : ℕ → ℝ) (hf : ∀ r, 0 ≤ f r)
    (hs : Summable f) (Y : ℝ) :
    (∑' r : ℕ, if (r : ℝ) ≤ Y then f r else 0) +
      (∑' r : ℕ, if Y < (r : ℝ) then f r else 0) = ∑' r, f r := by
  have hhead : Summable (fun r : ℕ => if (r : ℝ) ≤ Y then f r else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro r; split_ifs; exact hf r; exact le_rfl
    · intro r; split_ifs; exact le_rfl; exact hf r
  have htail : Summable (fun r : ℕ => if Y < (r : ℝ) then f r else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro r; split_ifs; exact hf r; exact le_rfl
    · intro r; split_ifs; exact le_rfl; exact hf r
  rw [← hhead.tsum_add htail]
  apply tsum_congr
  intro r
  by_cases hr : (r : ℝ) ≤ Y
  · simp [hr, not_lt_of_ge hr]
  · simp [hr, lt_of_not_ge hr]

/-- After any fixed positive logarithmic truncation, at least half the P
harmonic mass remains. The constants precede the exceptional Q-slot. -/
theorem harmonicP_small_mass (D : BandData) (hD : D.Valid)
    (hell : D.geometry.ell = 1) (sigma : ℝ) (hsigma : 0 < sigma) :
    ∀ᶠ x : ℝ in atTop,
      D.harmonicP x / 2 ≤
        ∑' r : ℕ, if (r : ℝ) ≤ x ^ sigma then
          groupHarmonicTerm D.geometry (D.groups x) r else 0 := by
  obtain ⟨CP, htail⟩ := harmonicP_tail D hD sigma hsigma
  obtain ⟨_, hsum⟩ := harmonicP_summable_polylog D hD
  filter_upwards [harmonicP_ge_one D hD hell, hsum, htail,
    Erdos821.S56Core.group_exponential_tail_saving D.geometry sigma 0 CP 1 hsigma,
    Erdos821.S56Core.tendsto_L.eventually (eventually_ge_atTop 2)]
    with x hP hs ht hsave hL
  have htailhalf : (∑' r : ℕ, if x ^ sigma < (r : ℝ) then
      groupHarmonicTerm D.geometry (D.groups x) r else 0) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-sigma * L x ^ (1 - D.geometry.d)) * L x ^ CP := ht
      _ ≤ L x ^ (-1 : ℝ) := by
        simpa only [zero_mul, add_zero, mul_comm] using hsave
      _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hL
  have heq := tsum_head_add_tail (groupHarmonicTerm D.geometry (D.groups x))
    (groupHarmonicTerm_nonneg D.geometry (D.groups x)) hs.1 (x ^ sigma)
  change _ + _ = D.harmonicP x at heq
  linarith

theorem geometry_harmonicP_small_mass (C : CandidateData) (δ : ℝ) (hC : C.Geometry δ)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    ∀ᶠ x : ℝ in atTop,
      C.bands.harmonicP x / 2 ≤
        ∑' r : ℕ, if (r : ℝ) ≤ x ^ sigma then
          groupHarmonicTerm C.bands.geometry (C.bands.groups x) r else 0 := by
  rcases hC with ⟨hD, _, _, _, _, _, _, _, _, _, hell, _⟩
  exact harmonicP_small_mass C.bands hD hell sigma hsigma

end Erdos821.P7Core

