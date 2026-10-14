import Erdos821.P6Off.ShiftBound
import Erdos821.P6Off.Growth

noncomputable section
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem endpointBound_mono (x C C' tau eta : ℝ) (F : Endpoint)
    (hx : 1 ≤ L x) (hC : C ≤ C') (hF : EndpointBound x C tau eta F) :
    EndpointBound x C' tau eta F := by
  obtain ⟨htau, htaueta, heta, hcoef, hrough, hr, hfreq0, hfreq1, hlo, hlohi, hhi⟩ := hF
  have hp : L x ^ C ≤ L x ^ C' := Real.rpow_le_rpow_of_exponent_le hx hC
  exact ⟨htau, htaueta, heta, fun n => ⟨(hcoef n).1.trans hp, (hcoef n).2.trans hp⟩,
    hrough, hr.trans hp, hfreq0.trans hp, hfreq1.trans hp, hlo, hlohi, hhi⟩

/-- Uniform endpoint bounds for every Fourier frequency in the fixed main
range. A single exponent C' controls coefficients, moduli and all twists. -/
theorem eventually_shiftEndpoint_frequency_bounds (C Cf Cm : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (U lo hi rho sigma tau eta : ℝ) (xi : Fin 3 → ℝ) (c alpha : ℕ → ℂ)
        (r : ℕ) (hr : 0 < r) (chi : DirichletCharacter ℂ r),
        0 < tau → tau < eta → eta < 1 / 4 →
        x ^ tau ≤ lo → lo ≤ hi → hi ≤ x ^ eta →
        (∀ n, ‖alpha n‖ ≤ L x ^ C ∧ ‖c n‖ ≤ L x ^ C) →
        (∀ n, alpha n ≠ 0 → rough (W x) n) →
        |rho| ≤ L x ^ C → |sigma| ≤ L x ^ C → ‖xi‖ ≤ L x ^ Cf →
        (r : ℝ) ≤ L x ^ Cm →
        let C' := max (max C Cf + 1) Cm;
        EndpointBound x C' tau eta
          (shiftEndpoint U lo hi rho sigma (-2 * Real.pi * xi 1) c alpha r hr chi) ∧
        EndpointBound x C' tau eta
          (shiftEndpoint U lo hi rho sigma (2 * Real.pi * xi 0) c alpha r hr chi) ∧
        |rho + 2 * Real.pi * xi 2| ≤ L x ^ C' ∧ |rho| ≤ L x ^ C' := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_frequency_power C Cf, hL.eventually (eventually_ge_atTop 1)] with x hfreq hx
  intro U lo hi rho sigma tau eta xi c alpha r hr chi htau htaueta heta hlo hlohi hhi hcoef hrough hrho hsigma hxi hrbound
  let C' := max (max C Cf + 1) Cm
  have hCC' : C ≤ C' := by
    unfold C'
    exact (le_max_left C Cf).trans ((by linarith : max C Cf ≤ max C Cf + 1).trans (le_max_left _ _))
  have hp : L x ^ C ≤ L x ^ C' := Real.rpow_le_rpow_of_exponent_le hx hCC'
  have hpFreq : L x ^ (max C Cf + 1) ≤ L x ^ C' :=
    Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
  have hpMod : L x ^ Cm ≤ L x ^ C' := Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)
  have hcoefs : ∀ n, ‖alpha n‖ ≤ L x ^ C' ∧ ‖c n‖ ≤ L x ^ C' :=
    fun n => ⟨(hcoef n).1.trans hp, (hcoef n).2.trans hp⟩
  have hcomp (i : Fin 3) : |xi i| ≤ L x ^ Cf := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm xi i).trans hxi
  refine ⟨?_, ?_, ?_, hrho.trans hp⟩
  · apply shiftEndpoint_bound x U lo hi rho sigma (-2 * Real.pi * xi 1) C' tau eta c alpha r hr chi
      htau htaueta heta hcoefs hrough (hrbound.trans hpMod) _ (hsigma.trans hp) hlo hlohi hhi
    have h := (hfreq rho (-(xi 1)) hrho (by simpa using hcomp 1)).trans hpFreq
    simpa only [mul_neg, neg_mul] using h
  · exact shiftEndpoint_bound x U lo hi rho sigma (2 * Real.pi * xi 0) C' tau eta c alpha r hr chi
      htau htaueta heta hcoefs hrough (hrbound.trans hpMod)
      ((hfreq rho (xi 0) hrho (hcomp 0)).trans hpFreq) (hsigma.trans hp) hlo hlohi hhi
  · exact (hfreq rho (xi 2) hrho (hcomp 2)).trans hpFreq


end Erdos821.P6Off
