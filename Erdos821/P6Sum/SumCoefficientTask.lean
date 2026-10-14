import Erdos821.S56.SumCoefficientTask

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Sum

private lemma sum_ite_and_mul {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q]
    (f : α → ℂ) (g : β → ℂ) :
    (∑ a, ∑ b, if P a ∧ Q b then f a * g b else 0) =
      (∑ a, if P a then f a else 0) * (∑ b, if Q b then g b else 0) := by
  classical
  have h (a : α) (b : β) :
      (if P a ∧ Q b then f a * g b else 0) =
        (if P a then f a else 0) * (if Q b then g b else 0) := by
    by_cases hp : P a <;> by_cases hq : Q b <;> simp [hp, hq]
  simp_rw [h]
  calc
    (∑ a, ∑ b, (if P a then f a else 0) * (if Q b then g b else 0)) =
        ∑ a, (if P a then f a else 0) * (∑ b, if Q b then g b else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
    _ = _ := by rw [Finset.sum_mul]

theorem sumCoefficientTask_proof : Erdos821.S56Core.SumCoefficientTask := by
  intro ι κ _ _ _ _ A B _ _ valA valB weightA weightB hvalA hvalB t
  letI : ∀ s : ι ⊕ κ, Fintype (Sum.elim A B s) :=
    fun s => Erdos821.S56Core.sumCoordinateFintype A B s
  let val : ∀ s : ι ⊕ κ, Sum.elim A B s → ℕ := fun s =>
    match s with
    | Sum.inl i => valA i
    | Sum.inr j => valB j
  let weight : ∀ s : ι ⊕ κ, Sum.elim A B s → ℂ := fun s =>
    match s with
    | Sum.inl i => weightA i
    | Sum.inr j => weightB j
  let e : (∀ s : ι ⊕ κ, Sum.elim A B s) ≃
      ((∀ i, A i) × (∀ j, B j)) :=
    Equiv.sumPiEquivProdPi (Sum.elim A B)
  change Erdos821.S56Core.productCoefficient (Sum.elim A B) val weight t = _
  have he_left (z : (∀ i, A i) × (∀ j, B j)) (i : ι) :
      e.symm z (Sum.inl i) = z.1 i := by
    exact congrFun (congrArg Prod.fst (e.apply_symm_apply z)) i
  have he_right (z : (∀ i, A i) × (∀ j, B j)) (j : κ) :
      e.symm z (Sum.inr j) = z.2 j := by
    exact congrFun (congrArg Prod.snd (e.apply_symm_apply z)) j
  have hprod (z : (∀ i, A i) × (∀ j, B j)) :
      (∏ s : ι ⊕ κ, val s (e.symm z s)) =
        (∏ i, valA i (z.1 i)) * ∏ j, valB j (z.2 j) := by
    rw [Fintype.prod_sum_type]
    simp only [val]
    simp_rw [he_left, he_right]
  have hweight (z : (∀ i, A i) × (∀ j, B j)) :
      (∏ s : ι ⊕ κ, weight s (e.symm z s)) =
        (∏ i, weightA i (z.1 i)) * ∏ j, weightB j (z.2 j) := by
    rw [Fintype.prod_sum_type]
    simp only [weight]
    simp_rw [he_left, he_right]
  have hposA (z : ∀ i, A i) : 0 < ∏ i, valA i (z i) :=
    Finset.prod_pos (fun i _ => hvalA i (z i))
  have hposB (z : ∀ j, B j) : 0 < ∏ j, valB j (z j) :=
    Finset.prod_pos (fun j _ => hvalB j (z j))
  conv_lhs => unfold Erdos821.S56Core.productCoefficient
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [hprod, hweight]
  calc
    _ = ∑ zA : (∀ i, A i), ∑ zB : (∀ j, B j),
        ∑ pr ∈ t.divisorsAntidiagonal,
          if pr.1 = ∏ i, valA i (zA i) ∧ pr.2 = ∏ j, valB j (zB j)
          then (∏ i, weightA i (zA i)) * ∏ j, weightB j (zB j) else 0 := by
      apply Finset.sum_congr rfl
      intro zA _
      apply Finset.sum_congr rfl
      intro zB _
      exact (Erdos821.S56Core.select_divisor_pair t _ _ (hposA zA) (hposB zB)
        ((∏ i, weightA i (zA i)) * ∏ j, weightB j (zB j))).symm
    _ = ∑ zA : (∀ i, A i), ∑ pr ∈ t.divisorsAntidiagonal,
        ∑ zB : (∀ j, B j),
          if pr.1 = ∏ i, valA i (zA i) ∧ pr.2 = ∏ j, valB j (zB j)
          then (∏ i, weightA i (zA i)) * ∏ j, weightB j (zB j) else 0 := by
      apply Finset.sum_congr rfl
      intro zA _
      exact Finset.sum_comm
    _ = ∑ pr ∈ t.divisorsAntidiagonal,
        ∑ zA : (∀ i, A i), ∑ zB : (∀ j, B j),
          if pr.1 = ∏ i, valA i (zA i) ∧ pr.2 = ∏ j, valB j (zB j)
          then (∏ i, weightA i (zA i)) * ∏ j, weightB j (zB j) else 0 := by
      exact Finset.sum_comm
    _ = ∑ pr ∈ t.divisorsAntidiagonal,
        (∑ zA : (∀ i, A i),
          if pr.1 = ∏ i, valA i (zA i) then ∏ i, weightA i (zA i) else 0) *
        (∑ zB : (∀ j, B j),
          if pr.2 = ∏ j, valB j (zB j) then ∏ j, weightB j (zB j) else 0) := by
      apply Finset.sum_congr rfl
      intro pr _
      exact sum_ite_and_mul
        (P := fun zA : ∀ i, A i => pr.1 = ∏ i, valA i (zA i))
        (Q := fun zB : ∀ j, B j => pr.2 = ∏ j, valB j (zB j))
        (f := fun zA : ∀ i, A i => ∏ i, weightA i (zA i))
        (g := fun zB : ∀ j, B j => ∏ j, weightB j (zB j))
    _ = _ := by simp only [Erdos821.S56Core.productCoefficient, eq_comm]


end Erdos821.P6Sum
