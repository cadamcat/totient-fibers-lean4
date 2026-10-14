import Mathlib

namespace Erdos821.S56
open scoped BigOperators

/-- Character orthogonality imposes the determinant's congruence exactly on units. -/
theorem character_congruence_proved (r : ℕ) [NeZero r] (m m' : ℕ)
    (hm : IsUnit (m : ZMod r)) (hm' : IsUnit (m' : ZMod r)) :
    (if (m : ZMod r) = (m' : ZMod r) then (1 : ℂ) else 0) =
      (∑ χ : DirichletCharacter ℂ r, χ (m : ZMod r) * star (χ (m' : ZMod r))) /
        (r.totient : ℂ) := by
  classical
  have hstar (χ : DirichletCharacter ℂ r) : χ (m' : ZMod r)⁻¹ = star (χ (m' : ZMod r)) := by
    have hnorm : ‖χ (m' : ZMod r)‖ = 1 := by
      simpa only [hm'.unit_spec] using χ.unit_norm_eq_one hm'.unit
    have hmul : χ (m' : ZMod r)⁻¹ * χ (m' : ZMod r) = 1 := by
      rw [← map_mul, (m' : ZMod r).inv_mul_of_unit hm', map_one]
    rw [eq_inv_of_mul_eq_one_left hmul, Complex.inv_eq_conj hnorm]
    rfl
  have hsum : (∑ χ : DirichletCharacter ℂ r, χ (m : ZMod r) * star (χ (m' : ZMod r))) =
      if (m' : ZMod r) = (m : ZMod r) then (r.totient : ℂ) else 0 := by
    have hh := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hm' (m : ZMod r)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro χ _
    rw [hstar]
    ring
  have hphi : (r.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos r)).ne'
  rw [hsum]
  by_cases h : (m : ZMod r) = (m' : ZMod r)
  · simp [h, hphi]
  · have h' : (m' : ZMod r) ≠ (m : ZMod r) := Ne.symm h
    simp [h, h']


end Erdos821.S56
