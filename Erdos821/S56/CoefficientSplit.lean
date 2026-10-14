import Mathlib
import Erdos821.S56.ProductError

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core

def productCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Type*) [∀ i, Fintype (A i)]
    (val : ∀ i, A i → ℕ) (weight : ∀ i, A i → ℂ) (v : ℕ) : ℂ :=
  ∑ z : ∀ i, A i, if (∏ i, val i (z i)) = v then ∏ i, weight i (z i) else 0

theorem select_divisor_pair (v a b : ℕ) (ha : 0 < a) (hb : 0 < b) (w : ℂ) :
    (∑ pr ∈ v.divisorsAntidiagonal, if pr.1 = a ∧ pr.2 = b then w else 0) =
      if a * b = v then w else 0 := by
  have hiff (pr : ℕ × ℕ) : (pr.1 = a ∧ pr.2 = b) ↔ pr = (a, b) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact Prod.ext h1 h2
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  simp_rw [hiff]
  rw [Finset.sum_ite_eq']
  by_cases hp : a * b = v
  · have hv : v ≠ 0 := by rw [← hp]; exact (mul_pos ha hb).ne'
    have hmem : (a, b) ∈ v.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨hp, hv⟩
    rw [ite_eq_left hmem, ite_eq_left hp]
  · have hmem : (a, b) ∉ v.divisorsAntidiagonal :=
      fun h => hp (Nat.mem_divisorsAntidiagonal.mp h).1
    rw [ite_eq_right hmem, ite_eq_right hp]

/-- Splitting labelled coordinates gives exact multiplicative convolution.
All factorial normalizations can be retained in either coefficient afterwards. -/
theorem product_coefficient_split {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Type*) [∀ i, Fintype (A i)]
    (val : ∀ i, A i → ℕ) (weight : ∀ i, A i → ℂ) (p : ι → Prop) [DecidablePred p]
    (hval : ∀ i a, 0 < val i a) (v : ℕ) :
    productCoefficient A val weight v =
      ∑ pr ∈ v.divisorsAntidiagonal,
        productCoefficient (fun i : {i // p i} => A i.val)
          (fun i => val i.val) (fun i => weight i.val) pr.1 *
        productCoefficient (fun i : {i // ¬p i} => A i.val)
          (fun i => val i.val) (fun i => weight i.val) pr.2 := by
  let e := Equiv.piEquivPiSubtypeProd p A
  have he_pos (zz : (∀ i : {i // p i}, A i.val) × (∀ i : {i // ¬p i}, A i.val))
      (i : {i // p i}) : e.symm zz i.val = zz.1 i :=
    congrFun (congrArg Prod.fst (e.apply_symm_apply zz)) i
  have he_neg (zz : (∀ i : {i // p i}, A i.val) × (∀ i : {i // ¬p i}, A i.val))
      (i : {i // ¬p i}) : e.symm zz i.val = zz.2 i :=
    congrFun (congrArg Prod.snd (e.apply_symm_apply zz)) i
  have hprod (z : ∀ i, A i) : (∏ i, val i (z i)) =
      (∏ i : {i // p i}, val i.val (z i.val)) * ∏ i : {i // ¬p i}, val i.val (z i.val) :=
    (Fintype.prod_subtype_mul_prod_subtype p (fun i => val i (z i))).symm
  have hweight (z : ∀ i, A i) : (∏ i, weight i (z i)) =
      (∏ i : {i // p i}, weight i.val (z i.val)) * ∏ i : {i // ¬p i}, weight i.val (z i.val) :=
    (Fintype.prod_subtype_mul_prod_subtype p (fun i => weight i (z i))).symm
  unfold productCoefficient
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [hprod, hweight]
  simp only [he_pos, he_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext z; simp)
  intro z _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext z; simp)
  intro z' _
  have ha : 0 < ∏ i : {i // p i}, val i.val (z i) := Finset.prod_pos (fun i _ => hval _ _)
  have hb : 0 < ∏ i : {i // ¬p i}, val i.val (z' i) := Finset.prod_pos (fun i _ => hval _ _)
  have hselect := select_divisor_pair v _ _ ha hb
    ((∏ i : {i // p i}, weight i.val (z i)) * ∏ i : {i // ¬p i}, weight i.val (z' i))
  rw [← hselect]
  apply Finset.sum_congr rfl
  intro pr _
  have hrev1 : (pr.1 = ∏ i : {i // p i}, val i.val (z i)) ↔
      (∏ i : {i // p i}, val i.val (z i)) = pr.1 := eq_comm
  have hrev2 : (pr.2 = ∏ i : {i // ¬p i}, val i.val (z' i)) ↔
      (∏ i : {i // ¬p i}, val i.val (z' i)) = pr.2 := eq_comm
  by_cases h1 : (∏ i : {i // p i}, val i.val (z i)) = pr.1 <;>
    by_cases h2 : (∏ i : {i // ¬p i}, val i.val (z' i)) = pr.2 <;>
      simp only [hrev1, hrev2, h1, h2, true_and, false_and, and_false,
        ite_true, ite_false, zero_mul, mul_zero]


theorem product_coefficient_norm_count {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Type*)
    [∀ i, Fintype (A i)] (val : ∀ i, A i → ℕ) (weight : ∀ i, A i → ℂ)
    (hw : ∀ i a, ‖weight i a‖ ≤ 1) (v : ℕ) :
    ‖productCoefficient A val weight v‖ ≤
      ((Finset.univ.filter (fun z : ∀ i, A i => (∏ i, val i (z i)) = v)).card : ℝ) := by
  unfold productCoefficient
  calc
    _ ≤ ∑ z : ∀ i, A i,
        ‖if (∏ i, val i (z i)) = v then ∏ i, weight i (z i) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ z : ∀ i, A i, if (∏ i, val i (z i)) = v then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs
      · simpa using product_norm_bound Finset.univ (fun i => weight i (z i)) 1 (by norm_num)
          (fun i _ => hw i (z i))
      · simp
    _ = _ := by simp


end Erdos821.S56Core
