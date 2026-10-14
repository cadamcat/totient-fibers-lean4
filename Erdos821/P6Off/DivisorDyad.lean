import Erdos821.P6Off.Correlation

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- The endpoint's actual alpha restriction gives exactly the same m sum as
an explicit dyadic range; no discrepancy is transferred to another sequence. -/
theorem restricted_divisor_sum (U : ℝ) (alpha f : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) :
    (∑ m ∈ n.divisors, restricted U alpha m * f m) =
      ∑ m ∈ dyad U, if m ∣ n then alpha m * f m else 0 := by
  calc
    _ = ∑ m ∈ n.divisors.filter (fun m => m ∈ dyad U), alpha m * f m := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m ∈ dyad U
      · simp [restricted, (mem_dyad_iff U m).mp hm, hm]
      · have hnot : ¬(U ≤ (m : ℝ) ∧ (m : ℝ) < 2 * U) :=
          fun h => hm ((mem_dyad_iff U m).mpr h)
        simp [restricted, hm, hnot]
    _ = ∑ m ∈ (dyad U).filter (fun m => m ∈ n.divisors), alpha m * f m := by
      congr 1
      ext m
      simp [and_comm]
    _ = _ := by simp [Finset.sum_filter, Nat.mem_divisors, hn]

theorem twistedHConvolution_as_dyad (P : Geometry) (G : PrimeGroups)
    (x U lo hi rho sigma xi : ℝ) (c alpha : ℕ → ℂ) (r : ℕ)
    (chi : DirichletCharacter ℂ r) (n : ℕ) (hn : n ≠ 0) :
    twistedHConvolution P G x U lo hi rho sigma xi c alpha r chi n =
      ∑ m ∈ dyad U,
        if m ∣ n then (alpha m * chi (m : ZMod r) * mellin m xi) *
          star (hCoefficient P G x lo hi rho sigma c (n / m)) else 0 := by
  unfold twistedHConvolution
  rw [Nat.sum_divisorsAntidiagonal (fun m h =>
    (restricted U alpha m * chi (m : ZMod r) * mellin m xi) *
      star (hCoefficient P G x lo hi rho sigma c h))]
  calc
    _ = ∑ m ∈ n.divisors, restricted U alpha m *
        (chi (m : ZMod r) * mellin m xi * star (hCoefficient P G x lo hi rho sigma c (n / m))) := by
      apply Finset.sum_congr rfl
      intro m _
      ac_rfl
    _ = _ := by
      rw [restricted_divisor_sum U alpha _ n hn]
      apply Finset.sum_congr rfl
      intro m _
      split_ifs <;> ac_rfl


end Erdos821.P6Off
