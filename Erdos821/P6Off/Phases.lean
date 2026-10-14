import Erdos821.P6Off.Localizer

noncomputable section
open scoped BigOperators

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

/-- The additive Fourier character in log(m/U) is a Mellin power and a
scalar of modulus one. -/
theorem e_log_div (xi m U : ℝ) (hm : 0 < m) (hU : 0 < U) :
    e (xi * Real.log (m / U)) =
      mellin m (2 * Real.pi * xi) * mellin U (-2 * Real.pi * xi) := by
  unfold Blueprint.Analytic.e Blueprint.Analytic.mellin
  rw [Real.log_div hm.ne' hU.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

def phaseScalar (U Z : ℝ) (xi : Fin 3 → ℝ) : ℂ :=
  mellin U (-2 * Real.pi * (xi 0 + xi 1)) * mellin Z (-2 * Real.pi * xi 2)

@[simp] theorem norm_phaseScalar (U Z : ℝ) (xi : Fin 3 → ℝ) :
    ‖phaseScalar U Z xi‖ = 1 := by
  simp [phaseScalar, norm_mul, Erdos821.P5Core.norm_mellin]

/-- The exact three powers used by the shifted endpoints. -/
theorem e_logCoordinates (xi : Fin 3 → ℝ) (U Z m m' z : ℝ)
    (hU : 0 < U) (hZ : 0 < Z) (hm : 0 < m) (hm' : 0 < m') (hz : 0 < z) :
    e (∑ i, xi i * logCoordinates U Z m m' z i) =
      phaseScalar U Z xi * mellin m (2 * Real.pi * xi 0) *
        mellin m' (2 * Real.pi * xi 1) * mellin z (2 * Real.pi * xi 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, logCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  change e (xi 0 * Real.log (m / U) +
    (xi 1 * Real.log (m' / U) + xi 2 * Real.log (z / Z))) = _
  have he (s t : ℝ) : e (s + t) = e s * e t := by
    simp [Blueprint.Analytic.e, add_mul, mul_add, Complex.exp_add]
  rw [he, he, e_log_div _ _ _ hm hU, e_log_div _ _ _ hm' hU, e_log_div _ _ _ hz hZ]
  unfold phaseScalar
  have hfreq : -2 * Real.pi * (xi 0 + xi 1) = -2 * Real.pi * xi 0 + -2 * Real.pi * xi 1 := by ring
  rw [hfreq, mellin_add]
  ac_rfl


end Erdos821.P6Off
