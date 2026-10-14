import Erdos821.Blueprint.TypeII

noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff

namespace Erdos821.S56Core
open Erdos821.Blueprint.Analytic

/-- A fixed compact smooth function has one Fourier coefficient function
with finite mass and every polynomial moment. These constants are fixed
before the number of slots, so multiplying O(T) transitions costs L^O(1). -/
theorem fixed_fourier (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ∃ a : ℝ → ℂ, Integrable a ∧
      (∀ n : ℕ, Integrable (fun xi => ‖xi‖ ^ n * ‖a xi‖)) ∧
      ∀ t, f t = ∫ xi, a xi * e (xi * t) := by
  let phi : 𝓢(ℝ, ℂ) := hc.toSchwartzMap (hf.of_le (by simp))
  let a : 𝓢(ℝ, ℂ) := 𝓕 phi
  refine ⟨a, a.integrable, fun n => a.integrable_pow_mul volume n, ?_⟩
  intro t
  have hinv : (𝓕⁻ (𝓕 phi : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = phi :=
    FourierTransform.fourierInv_fourier_eq phi
  have heval := congrArg (fun g : 𝓢(ℝ, ℂ) => g t) hinv
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', smul_eq_mul] at heval
  change phi t = _
  rw [← heval]
  apply integral_congr_ae
  filter_upwards with xi
  simp [a, e, real_inner_comm, mul_comm, mul_left_comm, mul_assoc]

/-- Moment domination makes every transition's Fourier truncation error
arbitrarily small without changing the fixed coefficient mass. -/
theorem fourier_tail_le_moment (a : ℝ → ℂ) (ha : Integrable a)
    (n : ℕ) (hm : Integrable (fun xi => ‖xi‖ ^ n * ‖a xi‖))
    (R : ℝ) (hR : 0 < R) :
    (∫ xi in {xi : ℝ | R < ‖xi‖}, ‖a xi‖) ≤
      (R ^ n)⁻¹ * ∫ xi, ‖xi‖ ^ n * ‖a xi‖ := by
  let s : Set ℝ := {xi : ℝ | R < ‖xi‖}
  have hs : MeasurableSet s := measurableSet_lt measurable_const continuous_norm.measurable
  have hpoint : (fun xi => ‖a xi‖) ≤ᵐ[volume.restrict s]
      fun xi => (R ^ n)⁻¹ * (‖xi‖ ^ n * ‖a xi‖) := by
    filter_upwards [ae_restrict_mem hs] with xi hxi
    have hp := pow_le_pow_left₀ hR.le hxi.le n
    have hmul := mul_le_mul_of_nonneg_right hp (norm_nonneg (a xi))
    have hdiv : ‖a xi‖ ≤ (‖xi‖ ^ n * ‖a xi‖) / R ^ n :=
      (le_div_iff₀ (pow_pos hR n)).mpr (by simpa [mul_comm] using hmul)
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  calc
    _ ≤ ∫ xi in s, (R ^ n)⁻¹ * (‖xi‖ ^ n * ‖a xi‖) :=
      integral_mono_ae ha.norm.restrict (hm.const_mul _).restrict hpoint
    _ ≤ ∫ xi, (R ^ n)⁻¹ * (‖xi‖ ^ n * ‖a xi‖) := by
      apply setIntegral_le_integral (hm.const_mul _)
      filter_upwards with xi
      positivity
    _ = _ := integral_const_mul _ _


end Erdos821.S56Core
