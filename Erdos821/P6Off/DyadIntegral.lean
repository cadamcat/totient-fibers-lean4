import Erdos821.P6Off.DyadAtoms

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

/-- Exact Fourier integral for the literal dyadic determinant sum at one shift. -/
theorem determinantAtShift_eq_integral (P : Geometry) (G : PrimeGroups)
    (x E U V Z lo hi rho sigma : ℝ) (N : ℕ) (k : ℤ) (etae etan : ℝ → ℝ)
    (c alpha : ℕ → ℂ) (a : (Fin 3 → ℝ) → ℂ) (hk : k ≠ 0) (hU : 0 < U) (hZ : 0 < Z)
    (ha : Integrable a)
    (hF : ∀ t, pulledCutoff U V Z E k etae etan logLocalizer t =
      ∫ xi, a xi * e (∑ j, xi j * t j)) :
    determinantAtShift P G x E U V Z lo hi rho sigma N k etae etan c alpha =
      ∫ xi, a xi * frequencyDyad P G x U Z lo hi rho sigma xi N (2 * k.natAbs) k c alpha := by
  rw [determinantAtShift_as_weighted_cutoff P G x E U V Z lo hi rho sigma N k etae etan c alpha hk hU hZ,
    finite_Fourier_sum _ _ _ _ a ha hF]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xi => by dsimp only; rw [frequencySum_dyadAtoms])

/-- One dyad is bounded by its main-frequency correlation and the absolute
error mass on the complement of that frequency range. -/
theorem determinantAtShift_norm_le (P : Geometry) (G : PrimeGroups)
    (x E U V Z lo hi rho sigma : ℝ) (N : ℕ) (k : ℤ) (etae etan : ℝ → ℝ)
    (c alpha : ℕ → ℂ) (a : (Fin 3 → ℝ) → ℂ) (hk : k ≠ 0) (hU : 0 < U) (hZ : 0 < Z)
    (ha : Integrable a)
    (hF : ∀ t, pulledCutoff U V Z E k etae etan logLocalizer t =
      ∫ xi, a xi * e (∑ j, xi j * t j))
    (S : Set (Fin 3 → ℝ)) (hS : MeasurableSet S) (M : ℝ)
    (hmain : ∀ xi ∈ S,
      ‖frequencyDyad P G x U Z lo hi rho sigma xi N (2 * k.natAbs) k c alpha‖ ≤ M) :
    ‖determinantAtShift P G x E U V Z lo hi rho sigma N k etae etan c alpha‖ ≤
      (∫ xi in S, ‖a xi‖) * M + (∫ xi in Sᶜ, ‖a xi‖) *
        absoluteDeterminantDyad P G x U Z lo hi rho sigma N k dyadicCutoff c alpha := by
  rw [determinantAtShift_eq_integral P G x E U V Z lo hi rho sigma N k etae etan c alpha a hk hU hZ ha hF]
  have hfrequency : (fun xi => a xi * frequencyDyad P G x U Z lo hi rho sigma xi N (2 * k.natAbs) k c alpha) =
      (fun xi => a xi * frequencySum (dyadIndexSet N U)
        (dyadAtomWeight P G x Z lo hi rho sigma (2 * k.natAbs) k c alpha)
        (fun i => logCoordinates U Z i.2.1 i.2.2 i.1) xi) := by
    funext xi
    rw [frequencySum_dyadAtoms]
  rw [hfrequency]
  have hbound := frequency_integral_bound (dyadIndexSet N U)
    (dyadAtomWeight P G x Z lo hi rho sigma (2 * k.natAbs) k c alpha)
    (fun i => logCoordinates U Z i.2.1 i.2.2 i.1) a ha S hS M
    (fun xi hxi => by rw [frequencySum_dyadAtoms]; exact hmain xi hxi)
  apply hbound.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left
  · exact norm_dyadAtoms_le_absolute P G x U Z lo hi rho sigma N (2 * k.natAbs) k c alpha
  · exact integral_nonneg (fun _ => norm_nonneg _)


end Erdos821.P6Off
