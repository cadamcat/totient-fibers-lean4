import Erdos821.P6Off.Convolution
import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem mellin_add (n s t : ℝ) : mellin n (s + t) = mellin n s * mellin n t := by
  simp [Blueprint.Analytic.mellin, mul_add, add_mul, Complex.exp_add]

theorem star_mellin (n t : ℝ) : star (mellin n t) = mellin n (-t) := by
  simp [Blueprint.Analytic.mellin, Complex.star_def, ← Complex.exp_conj] <;> congr 1 <;> ring

theorem mellin_mul_neg (n t : ℝ) : mellin n t * mellin n (-t) = 1 := by
  rw [← mellin_add]
  simp [Blueprint.Analytic.mellin]

/-- Conjugation changes the rough-slot frequency and residual together. -/
theorem star_roughCore (x lo hi sigma : ℝ) (c : ℕ → ℂ) (n : ℕ) :
    star (roughCore x lo hi sigma c n) =
      roughCore x lo hi (-sigma) (fun r => star (c r)) n := by
  unfold roughCore
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro pr _
  split_ifs
  · simp only [star_mul, star_mellin]
    ring
  · simp

/-- Mellin exponents after cross-pairing. -/
theorem endpoint_twist_factor (m h : ℝ) (hm : 0 < m) (hh : 0 < h) (rho xi : ℝ) :
    mellin (m * h) (-rho) * mellin m (rho + xi) =
      mellin m xi * mellin h (-rho) := by
  rw [Erdos821.P5Core.mellin_mul _ _ _ hm hh, mellin_add]
  calc
    _ = (mellin m rho * mellin m (-rho)) * mellin m xi * mellin h (-rho) := by ring
    _ = _ := by rw [mellin_mul_neg]; ring


end Erdos821.P6Off
