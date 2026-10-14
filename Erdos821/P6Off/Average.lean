import Erdos821.P6Off.Characters

noncomputable section
open scoped BigOperators

namespace Erdos821.P6Off

/-- The exact totient normalization makes character averaging cost-free. -/
theorem norm_character_average_le (r : ℕ) [NeZero r]
    (f : DirichletCharacter ℂ r → ℂ) (M : ℝ) (hbound : ∀ chi, ‖f chi‖ ≤ M) :
    ‖(r.totient : ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ r, f chi‖ ≤ M := by
  have hphi : 0 < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r)
  have hcard : Fintype.card (DirichletCharacter ℂ r) = r.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
  have hsum : ‖∑ chi : DirichletCharacter ℂ r, f chi‖ ≤ (r.totient : ℝ) * M := by
    calc
      _ ≤ ∑ chi : DirichletCharacter ℂ r, ‖f chi‖ := norm_sum_le _ _
      _ ≤ ∑ _chi : DirichletCharacter ℂ r, M := Finset.sum_le_sum (fun chi _ => hbound chi)
      _ = _ := by simp [hcard]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (r.totient : ℝ)⁻¹ * ((r.totient : ℝ) * M) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hphi.le)
    _ = _ := by field_simp


end Erdos821.P6Off
