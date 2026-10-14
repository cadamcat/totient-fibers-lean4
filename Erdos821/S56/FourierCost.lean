import Erdos821.S56.BranchFourier
import Erdos821.S56.ProcessedSlots

noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem branch_mass_polylog (D : BandData) (hD : D.Valid) (a : Bool → ℝ → ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ,
      (∑ delta : ProcessedIndex D x jstar → Bool,
        ∫ xi : ProcessedIndex D x jstar → ℝ,
          ‖branchFourierCoefficient (pureIndices D x jstar).card a delta xi‖) ≤ L x ^ C := by
  let M : ℝ := max 1 ((∫ xi : ℝ, ‖a false xi‖) + ∫ xi : ℝ, ‖a true xi‖)
  have hM : 1 ≤ M := le_max_left _ _
  have hmass : (∫ xi : ℝ, ‖a false xi‖) + (∫ xi : ℝ, ‖a true xi‖) ≤ M := le_max_right _ _
  have hmass0 : 0 ≤ (∫ xi : ℝ, ‖a false xi‖) + ∫ xi : ℝ, ‖a true xi‖ :=
    add_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (integral_nonneg (fun _ => norm_nonneg _))
  obtain ⟨C, hC, hc⟩ := processed_card_bound D hD
  refine ⟨C * Real.log M + 1, ?_, ?_⟩
  · have hlogM := Real.log_nonneg hM
    positivity
  · filter_upwards [hc, tendsto_L.eventually (eventually_ge_atTop 1)] with x hx hL
    intro jstar
    rw [branch_total_mass]
    calc
      _ ≤ M ^ (pureIndices D x jstar).card := pow_le_pow_left₀ hmass0 hmass _
      _ ≤ L x ^ (C * Real.log M) := polylog_of_loglog_count x C M _
        (zero_lt_one.trans_le hL) hM (hx jstar)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)

/-- A fixed coefficient's moments control the truncation error uniformly
in the argument where the transition is evaluated. -/
theorem fixed_fourier_truncation (f : ℝ → ℂ) (a : ℝ → ℂ) (ha : Integrable a)
    (hrep : ∀ t, f t = ∫ xi, a xi * e (xi * t))
    (n : ℕ) (hm : Integrable (fun xi => ‖xi‖ ^ n * ‖a xi‖))
    (R : ℝ) (hR : 0 < R) (t : ℝ) :
    ‖f t - ∫ xi in {xi : ℝ | ‖xi‖ ≤ R}, a xi * e (xi * t)‖ ≤
      (R ^ n)⁻¹ * ∫ xi, ‖xi‖ ^ n * ‖a xi‖ := by
  have hecont : Continuous (fun xi : ℝ => e (xi * t)) := by unfold e; fun_prop
  have hint : Integrable (fun xi : ℝ => a xi * e (xi * t)) :=
    ha.mono (ha.aestronglyMeasurable.mul hecont.aestronglyMeasurable)
      (Eventually.of_forall (fun xi => by simp only [norm_mul, norm_e, mul_one]; exact le_rfl))
  have hs : MeasurableSet {xi : ℝ | ‖xi‖ ≤ R} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have hc : ({xi : ℝ | ‖xi‖ ≤ R} : Set ℝ)ᶜ = {xi : ℝ | R < ‖xi‖} := by ext xi; simp
  rw [hrep t, ← integral_add_compl hs hint]
  simp only [add_sub_cancel_left]
  calc
    _ ≤ ∫ xi in {xi : ℝ | ‖xi‖ ≤ R}ᶜ, ‖a xi * e (xi * t)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ xi in {xi : ℝ | R < ‖xi‖}, ‖a xi‖ := by
      rw [hc]
      apply integral_congr_ae
      filter_upwards with xi
      simp only [norm_mul, norm_e, mul_one]
    _ ≤ _ := fourier_tail_le_moment a ha n hm R hR


theorem fourier_truncated_norm_le_mass (a : ℝ → ℂ) (ha : Integrable a)
    (R t : ℝ) :
    ‖∫ xi in {xi : ℝ | ‖xi‖ ≤ R}, a xi * e (xi * t)‖ ≤ ∫ xi, ‖a xi‖ := by
  calc
    _ ≤ ∫ xi in {xi : ℝ | ‖xi‖ ≤ R}, ‖a xi * e (xi * t)‖ := norm_integral_le_integral_norm _
    _ = ∫ xi in {xi : ℝ | ‖xi‖ ≤ R}, ‖a xi‖ := by
      apply integral_congr_ae
      filter_upwards with xi
      simp only [norm_mul, norm_e, mul_one]
    _ ≤ _ := setIntegral_le_integral ha.norm (Eventually.of_forall (fun _ => norm_nonneg _))

end Erdos821.S56Core
