import Erdos821.S56.Allocation
import Erdos821.S56.BandSize

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem slot_value_bounds (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (s : D.Slot x) :
    Real.exp (D.c₁ * D.scale x s.1.val) ≤ (z s).val ∧
      ((z s).val : ℝ) ≤ Real.exp (D.c₂ * D.scale x s.1.val) := by
  have hmem := (z s).property
  have hb : ⌈Real.exp (D.c₁ * D.scale x s.1.val)⌉₊ ≤ (z s).val ∧
      (z s).val ≤ ⌊Real.exp (D.c₂ * D.scale x s.1.val)⌋₊ := by
    unfold BandData.slotValues at hmem
    split_ifs at hmem
    · exact Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1
    · exact Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1
  exact ⟨Nat.ceil_le.mp hb.1, (Nat.le_floor_iff (Real.exp_pos _).le).mp hb.2⟩

theorem slot_log_bounds (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (s : D.Slot x) :
    D.c₁ * D.scale x s.1.val ≤ Real.log (z s).val ∧
      Real.log (z s).val ≤ D.c₂ * D.scale x s.1.val := by
  obtain ⟨hlo, hhi⟩ := slot_value_bounds D z s
  have hp : (0 : ℝ) < (z s).val := by exact_mod_cast slot_value_pos D z s
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hlo
  · simpa only [Real.log_exp] using Real.log_le_log hp hhi

theorem scale_pos (D : BandData) (hD : D.Valid) (x : ℝ) (hL : 0 < L x) (j : ℕ) :
    0 < D.scale x j := by
  have hs := hD.2.2.2.1
  have hratio : 0 < D.ratio := zero_lt_one.trans hD.2.2.2.2.1
  exact div_pos (mul_pos hs hL) (pow_pos hratio _)

theorem log_allocation (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : D.Slot x → Bool) :
    Real.log (allocationFactor D z delta) =
      ∑ s, if delta s then Real.log (z s).val else 0 := by
  have hp (s : D.Slot x) : (0 : ℝ) < (z s).val := by
    exact_mod_cast slot_value_pos D z s
  simp only [allocationFactor, Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro s _
    cases delta s <;> simp
  · intro s _
    cases delta s <;> simp [hp s, (hp s).ne']


end Erdos821.S56Core
