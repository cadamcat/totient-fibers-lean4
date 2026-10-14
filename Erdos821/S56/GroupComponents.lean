import Erdos821.S56.GroupParts

noncomputable section
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint.Analytic

theorem group_components (G : PrimeGroups) (u : ℕ) (hu : 0 < u) (q : ℝ)
    (t : Fin G.size → ℕ) :
    groupFreePart G u * groupPart G u = u ∧
      groupFreePart G (groupPart G u) = 1 ∧
      markWeight G q t u = markWeight G q t (groupPart G u) := by
  have hfree := groupFreePart_groupFree G u
  have hfp := groupFreePart_pos G u
  have hgp := groupPart_pos G u
  have hprod : groupFreePart G u * groupPart G u = u := by
    simpa only [mul_comm] using groupPart_mul_freePart G u hu
  have hparts := groupFreePart_mul G (groupFreePart G u) (groupPart G u) hfp hgp hfree
  rw [hprod] at hparts
  have hpure : groupFreePart G (groupPart G u) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hfp
    simpa only [mul_one] using hparts.symm
  have hweight := markWeight_mul G (groupFreePart G u) (groupPart G u) hfree q t
  rw [hprod] at hweight
  exact ⟨hprod, hpure, hweight⟩

theorem groupPart_dvd (G : PrimeGroups) (u : ℕ) (hu : 0 < u) : groupPart G u ∣ u :=
  ⟨groupFreePart G u, (groupPart_mul_freePart G u hu).symm⟩


end Erdos821.S56Core
