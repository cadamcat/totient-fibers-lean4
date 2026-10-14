import Erdos821.P6Off.DivisorDyad
import Erdos821.S56.CharacterCongruence

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

theorem character_congruence_nat (r : ℕ) [NeZero r] (m m' : ℕ)
    (hm : IsUnit (m : ZMod r)) (hm' : IsUnit (m' : ZMod r)) :
    (if Nat.ModEq r m m' then (1 : ℂ) else 0) =
      (∑ chi : DirichletCharacter ℂ r, chi (m : ZMod r) * star (chi (m' : ZMod r))) /
        (r.totient : ℂ) := by
  simpa only [ZMod.natCast_eq_natCast_iff] using
    Erdos821.S56.character_congruence_proved r m m' hm hm'

/-- Exact character projection for two coefficient sequences supported on units. -/
theorem finite_character_projection (r : ℕ) [NeZero r] (s t : Finset ℕ) (f g : ℕ → ℂ)
    (hf : ∀ m, f m ≠ 0 → IsUnit (m : ZMod r))
    (hg : ∀ m, g m ≠ 0 → IsUnit (m : ZMod r)) :
    (∑ m ∈ s, ∑ m' ∈ t, if Nat.ModEq r m m' then f m * star (g m') else 0) =
      (r.totient : ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ r,
        (∑ m ∈ s, f m * chi (m : ZMod r)) * star (∑ m' ∈ t, g m' * chi (m' : ZMod r)) := by
  have hpoint (m m' : ℕ) :
      (if Nat.ModEq r m m' then f m * star (g m') else 0) =
        (r.totient : ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ r,
          (f m * chi (m : ZMod r)) * star (g m' * chi (m' : ZMod r)) := by
    by_cases hf0 : f m = 0
    · simp [hf0]
    by_cases hg0 : g m' = 0
    · simp [hg0]
    calc
      _ = (if Nat.ModEq r m m' then (1 : ℂ) else 0) * (f m * star (g m')) := by
        split_ifs <;> simp
      _ = _ := by
        rw [character_congruence_nat r m m' (hf m hf0) (hg m' hg0)]
        simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro chi _
        rw [star_mul]
        ring
  simp_rw [hpoint]
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := t) (t := (Finset.univ : Finset (DirichletCharacter ℂ r)))]
  rw [Finset.sum_comm (s := s) (t := (Finset.univ : Finset (DirichletCharacter ℂ r)))]
  apply Finset.sum_congr rfl
  intro chi _
  exact Finset.sum_comm


end Erdos821.P6Off
