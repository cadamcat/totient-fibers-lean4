import Erdos821.S56.BlueprintInvariant

noncomputable section

namespace Erdos821.S56Core
open Erdos821.Blueprint.Analytic

/-- Removing a positive group-free divisor removes the same factor from the
outside part. This is the quotient form used by the finite slot split. -/
theorem groupFreePart_divisor_mul (G : PrimeGroups) (u e : ℕ)
    (hu : 0 < u) (he : 0 < e) (hd : e ∣ u) (hfree : GroupFree G e) :
    groupFreePart G u = e * groupFreePart G (u/e) := by
  have hh : 0 < u/e := Nat.div_pos (Nat.le_of_dvd hu hd) he
  simpa only [Nat.mul_div_cancel' hd] using groupFreePart_mul G e (u/e) he hh hfree

theorem groupFreePart_divisor (G : PrimeGroups) (u e : ℕ)
    (hu : 0 < u) (he : 0 < e) (hd : e ∣ u) (hfree : GroupFree G e) :
    groupFreePart G (u/e) = groupFreePart G u / e := by
  rw [groupFreePart_divisor_mul G u e hu he hd hfree, Nat.mul_div_right _ he]

theorem markWeight_divisor (G : PrimeGroups) (u e : ℕ)
    (hd : e ∣ u) (hfree : GroupFree G e) (q : ℝ) (t : Fin G.size → ℕ) :
    markWeight G q t u = markWeight G q t (u/e) := by
  simpa only [Nat.mul_div_cancel' hd] using markWeight_mul G e (u/e) hfree q t


end Erdos821.S56Core
