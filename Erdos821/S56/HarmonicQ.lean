import Erdos821.S56.SlotBounds

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint

/-- The literal labelled-list harmonic mass factors slot by slot. -/
theorem tuple_harmonic_factorization (D : BandData) (x : ℝ) (jstar : ℕ) :
    (∑ z : D.Lists x jstar, (D.listProduct z : ℝ)⁻¹) =
      ∏ s : D.Slot x, ∑ v ∈ D.slotValues x jstar s, (v : ℝ)⁻¹ := by
  calc
    _ = ∑ z : D.Lists x jstar, ∏ s, ((z s).val : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [BandData.listProduct, Nat.cast_prod, Finset.prod_inv_distrib]
    _ = ∏ s : D.Slot x, ∑ v : D.SlotValue x jstar s, (v.val : ℝ)⁻¹ :=
      (Fintype.prod_sum (fun s (v : D.SlotValue x jstar s) => (v.val : ℝ)⁻¹)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro s _
      exact Finset.sum_coe_sort (D.slotValues x jstar s) (fun v : ℕ => (v : ℝ)⁻¹)

/-- Every finite ordinary product range is dominated by harmonicQ. -/
theorem harmonic_aQ_le (D : BandData) (x : ℝ) (jstar N : ℕ) :
    (∑ v ∈ Finset.Icc 1 N, D.aQ x jstar v / v) ≤ D.harmonicQ x jstar := by
  have hcard (v : ℕ) :
      ((Finset.univ.filter (fun z : D.Lists x jstar => D.listProduct z = v)).card : ℝ) / v =
        ∑ z : D.Lists x jstar, if D.listProduct z = v then (v : ℝ)⁻¹ else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  simp only [BandData.aQ, mul_div_assoc]
  rw [← Finset.mul_sum]
  rw [BandData.harmonicQ, ← tuple_harmonic_factorization]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp_rw [hcard]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z _
  rw [Finset.sum_ite_eq]
  split_ifs
  · exact le_rfl
  · positivity


end Erdos821.S56Core
