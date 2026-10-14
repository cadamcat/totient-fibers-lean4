import Erdos821.P6Off.DyadIntegral

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

/-- The separated main term and Fourier tail give a uniform logarithmic
power bound on the literal dyadic determinant sum at one signed shift. -/
theorem determinantAtShift_power_bound (P : Geometry) (G : PrimeGroups)
    (x E U V Z lo hi rho sigma Cf Kf D At Ct Kmain Kat Ktail : ℝ)
    (N : ℕ) (k : ℤ) (etae etan : ℝ → ℝ) (c alpha : ℕ → ℂ)
    (a : (Fin 3 → ℝ) → ℂ) (hk : k ≠ 0) (hU : 0 < U) (hZ : 0 < Z) (hL : 0 < L x)
    (hKmain : 0 ≤ Kmain) (hKat : 0 ≤ Kat) (hKtail : 0 ≤ Ktail)
    (ha : Integrable a)
    (hF : ∀ t, pulledCutoff U V Z E k etae etan logLocalizer t =
      ∫ xi, a xi * e (∑ j, xi j * t j))
    (hL1 : (∫ xi, ‖a xi‖) ≤ L x ^ Kf)
    (htail : (∫ xi in {xi : Fin 3 → ℝ | L x ^ Cf < ‖xi‖}, ‖a xi‖) ≤ Kat * L x ^ (-At))
    (hmain : ∀ xi : Fin 3 → ℝ, ‖xi‖ ≤ L x ^ Cf →
      ‖frequencyDyad P G x U Z lo hi rho sigma xi N (2 * k.natAbs) k c alpha‖ ≤
        Kmain * Z * L x ^ (-D))
    (habsolute : absoluteDeterminantDyad P G x U Z lo hi rho sigma N k dyadicCutoff c alpha ≤
      Ktail * Z * L x ^ Ct) :
    ‖determinantAtShift P G x E U V Z lo hi rho sigma N k etae etan c alpha‖ ≤
      Kmain * Z * L x ^ (Kf - D) + Kat * Ktail * Z * L x ^ (Ct - At) := by
  let S := {xi : Fin 3 → ℝ | ‖xi‖ ≤ L x ^ Cf}
  have hS : MeasurableSet S := (isClosed_le continuous_norm continuous_const).measurableSet
  have hcompl : Sᶜ = {xi : Fin 3 → ℝ | L x ^ Cf < ‖xi‖} := by ext xi; simp [S]
  have hmass : (∫ xi in S, ‖a xi‖) ≤ L x ^ Kf :=
    (setIntegral_le_integral ha.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).trans hL1
  have htail' : (∫ xi in Sᶜ, ‖a xi‖) ≤ Kat * L x ^ (-At) := by rw [hcompl]; exact htail
  have hbound := determinantAtShift_norm_le P G x E U V Z lo hi rho sigma N k etae etan
    c alpha a hk hU hZ ha hF S hS (Kmain * Z * L x ^ (-D)) (fun xi hxi => hmain xi hxi)
  apply hbound.trans
  calc
    _ ≤ L x ^ Kf * (Kmain * Z * L x ^ (-D)) +
        (Kat * L x ^ (-At)) * (Ktail * Z * L x ^ Ct) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hmass (by positivity)
      · apply mul_le_mul htail' habsolute
        · unfold absoluteDeterminantDyad
          positivity
        · positivity
    _ = _ := by
      have hmainpow : L x ^ Kf * L x ^ (-D) = L x ^ (Kf - D) := by
        rw [← Real.rpow_add hL]
        congr 1 <;> ring
      have htailpow : L x ^ (-At) * L x ^ Ct = L x ^ (Ct - At) := by
        rw [← Real.rpow_add hL]
        congr 1 <;> ring
      calc
        _ = Kmain * Z * (L x ^ Kf * L x ^ (-D)) +
            Kat * Ktail * Z * (L x ^ (-At) * L x ^ Ct) := by ring
        _ = _ := by rw [hmainpow, htailpow]


end Erdos821.P6Off
