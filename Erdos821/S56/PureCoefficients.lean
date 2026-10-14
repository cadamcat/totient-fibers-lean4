import Erdos821.S56.CoefficientSplit
import Erdos821.S56.MultiplicityTasks
import Erdos821.S56.CoreBound
import Erdos821.S56.BandSize

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def pureCoefficient (D : BandData) (x : ℝ) (S : Finset (D.Slot x))
    (xi : S → ℝ) (v : ℕ) : ℂ :=
  productCoefficient (fun s : S => {p : ℕ // p ∈ D.band x s.val.1.val})
    (fun _ p => p.val) (fun s p => Erdos821.Blueprint.Analytic.mellin p.val (xi s)) v

theorem pure_coefficient_norm_count (D : BandData) (x : ℝ) (S : Finset (D.Slot x))
    (xi : S → ℝ) (v : ℕ) :
    ‖pureCoefficient D x S xi v‖ ≤
      ((Finset.univ.filter (fun z : PureLists D x S => pureListProduct D x S z = v)).card : ℝ) := by
  exact product_coefficient_norm_count
    (fun s : S => {p : ℕ // p ∈ D.band x s.val.1.val}) (fun _ p => p.val)
    (fun s p => Erdos821.Blueprint.Analytic.mellin p.val (xi s))
    (fun s p => (norm_mellin p.val (xi s)).le) v

/-- Every partial prime-slot coefficient has a fixed logarithmic bound,
uniform in its slot subset, product and all phase frequencies. -/
theorem pure_coefficients_polylog (hCount : PureSlotMultiplicityTask)
    (D : BandData) (hD : D.Valid) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (D.Slot x)) (xi : S → ℝ) (v : ℕ),
        ‖pureCoefficient D x S xi v‖ ≤ L x ^ C := by
  obtain ⟨Cf, hfact⟩ := band_factorial_bound D hD
  let C := max Cf 0 + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hCount D hD, hfact, tendsto_L.eventually (eventually_ge_atTop 1)] with x hx hf hL
  intro S xi v
  have hC : Cf ≤ C := by dsimp [C]; linarith [le_max_left Cf 0]
  exact (pure_coefficient_norm_count D x S xi v).trans
    ((hx S v).trans (hf.trans (Real.rpow_le_rpow_of_exponent_le hL hC)))

theorem factorial_normalization_le_one (D : BandData) (x : ℝ) :
    0 ≤ ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ ∧
      ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ ≤ 1 := by
  have hbase : 1 ≤ (D.r₀.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos D.r₀
  have hp : 1 ≤ (D.r₀.factorial : ℝ) ^ (D.last x + 1) := one_le_pow₀ hbase
  exact ⟨inv_nonneg.mpr (zero_le_one.trans hp), (inv_le_one₀ (zero_lt_one.trans_le hp)).mpr hp⟩

theorem normalized_pure_coefficient_bound (D : BandData) (x : ℝ) (S : Finset (D.Slot x))
    (xi : S → ℝ) (v : ℕ) :
    ‖(((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ : ℂ) * pureCoefficient D x S xi v‖ ≤
      ‖pureCoefficient D x S xi v‖ := by
  obtain ⟨hnonneg, hle⟩ := factorial_normalization_le_one D x
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg D.r₀.factorial : (0 : ℝ) ≤ D.r₀.factorial)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hle (norm_nonneg _)


end Erdos821.S56Core
