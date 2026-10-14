import Erdos821.P6Off.Endpoint
import Erdos821.P6Off.Twists

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- Both §5 endpoints use the original restricted alpha and the conjugated
residual, with only explicit character and Mellin factors changed. -/
def shiftEndpoint (U lo hi rho sigma xi : ℝ) (c alpha : ℕ → ℂ)
    (r : ℕ) (hr : 0 < r) (chi : DirichletCharacter ℂ r) : Endpoint where
  alpha := restricted U alpha
  residual := fun n => star (c n)
  modulus := r
  positive := hr
  chi := chi
  sigma₀ := rho + xi
  sigma₁ := -sigma
  lo := lo
  hi := hi

theorem star_real_cast (a : ℝ) : star (a : ℂ) = (a : ℂ) := by
  simp [Complex.star_def]

/-- Exact endpoint identification before the outer shifted correlation is summed. -/
theorem shiftEndpoint_identity (P : Geometry) (G : PrimeGroups)
    (x U lo hi rho sigma xi : ℝ) (c alpha : ℕ → ℂ)
    (r : ℕ) (hr : 0 < r) (chi : DirichletCharacter ℂ r) (n : ℕ)
    (hn : n ≠ 0) (hfree : ∀ m, alpha m ≠ 0 → GroupFree G m) :
    mellin n (-rho) * endpoint G x (shiftEndpoint U lo hi rho sigma xi c alpha r hr chi) n *
        markWeight G P.q (fun _ => P.ell) n =
      ∑ mh ∈ n.divisorsAntidiagonal,
        (restricted U alpha mh.1 * chi (mh.1 : ZMod r) * mellin mh.1 xi) *
          star (hCoefficient P G x lo hi rho sigma c mh.2) := by
  have hfree' : ∀ m, (shiftEndpoint U lo hi rho sigma xi c alpha r hr chi).alpha m ≠ 0 →
      GroupFree G m := by
    intro m hm
    apply hfree m
    change restricted U alpha m ≠ 0 at hm
    intro hzero
    exact hm (by simp [restricted, hzero])
  rw [endpoint_as_actual_convolution G x _ n hn hfree', Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mh hmh
  have heq := (Nat.mem_divisorsAntidiagonal.mp hmh).1
  have hmpos := Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hmh)
  have hhpos := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hmh)
  by_cases hα : restricted U alpha mh.1 = 0
  · simp [shiftEndpoint, hα]
  · have hmf := hfree' mh.1 hα
    have hweight : markWeight G P.q (fun _ => P.ell) n =
        markWeight G P.q (fun _ => P.ell) mh.2 := by
      rw [← heq, markWeight_mul G mh.1 mh.2 hmf]
    have htwist : mellin n (-rho) * mellin mh.1 (rho + xi) =
        mellin mh.1 xi * mellin mh.2 (-rho) := by
      rw [← heq, Nat.cast_mul]
      exact endpoint_twist_factor _ _ (by exact_mod_cast hmpos) (by exact_mod_cast hhpos) rho xi
    simp only [shiftEndpoint, hCoefficient, star_mul, star_mellin, star_roughCore,
      star_real_cast, hweight]
    calc
      _ = (restricted U alpha mh.1 * chi (mh.1 : ZMod r)) *
          (mellin n (-rho) * mellin mh.1 (rho + xi)) *
          roughCore x lo hi (-sigma) (fun r => star (c r)) (groupFreePart G mh.2) *
          (markWeight G P.q (fun _ => P.ell) mh.2 : ℂ) := by ac_rfl
      _ = _ := by rw [htwist]; ac_rfl


end Erdos821.P6Off
