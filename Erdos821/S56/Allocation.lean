import Erdos821.S56.BlueprintInvariant

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- A branch assigns only pure-prime slots to its small factor e. -/
def allocationFactor (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : D.Slot x → Bool) : ℕ :=
  ∏ s, if delta s then (z s).val else 1

theorem slot_value_pos (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (s : D.Slot x) : 0 < (z s).val := by
  have hmem := (z s).property
  have hlo : ⌈Real.exp (D.c₁ * D.scale x s.1.val)⌉₊ ≤ (z s).val := by
    unfold BandData.slotValues at hmem
    split_ifs at hmem
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1
  have hr : 0 < ((z s).val : ℝ) :=
    (Real.exp_pos _).trans_le (Nat.ceil_le.mp hlo)
  exact_mod_cast hr

theorem allocation_pos (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : D.Slot x → Bool) :
    0 < allocationFactor D z delta := by
  unfold allocationFactor
  apply Finset.prod_pos
  intro s _
  cases delta s
  · simp
  · simpa using slot_value_pos D z s

theorem allocation_product (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : D.Slot x → Bool) :
    allocationFactor D z delta * allocationFactor D z (fun s => !delta s) =
      D.listProduct z := by
  rw [allocationFactor, allocationFactor, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  cases delta s <;> simp

theorem groupFree_prod {ι : Type*} (G : PrimeGroups) (s : Finset ι) (f : ι → ℕ)
    (hfree : ∀ i ∈ s, GroupFree G (f i)) : GroupFree G (∏ i ∈ s, f i) := by
  intro p hp
  obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
  apply (G.prime g p hpg).prime.not_dvd_finsetProd
  intro i hi
  exact hfree i hi p hp

theorem allocation_groupFree (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : D.Slot x → Bool)
    (hdisjoint : ∀ j ≤ D.last x, ∀ g,
      Disjoint (D.band x j) ((D.groups x).primes g))
    (hexcept : ∀ s, s.1.val = jstar → s.2.val = 0 → delta s = false) :
    GroupFree (D.groups x) (allocationFactor D z delta) := by
  unfold allocationFactor
  apply groupFree_prod
  intro s _
  by_cases hd : delta s = true
  · rw [hd]
    simp only [Bool.true_eq_false, ↓reduceIte]
    have hnexception : ¬(s.1.val = jstar ∧ s.2.val = 0) := by
      rintro ⟨hs1, hs2⟩
      have hfalse := hexcept s hs1 hs2
      simp [hd] at hfalse
    have hz : (z s).val ∈ D.band x s.1.val := by
      have hmem := (z s).property
      simpa only [BandData.slotValues, if_neg hnexception] using hmem
    have hzprime : ((z s).val).Prime := (Finset.mem_filter.mp hz).2
    intro p hp hdiv
    obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
    have heq : p = (z s).val := (Nat.prime_dvd_prime_iff_eq
      ((D.groups x).prime g p hpg) hzprime).mp hdiv
    subst p
    exact Finset.disjoint_left.mp (hdisjoint s.1.val (by omega) g) hz hpg
  · have hd' : delta s = false := Bool.eq_false_iff.mpr hd
    rw [hd']
    simp only [Bool.false_eq_true, ↓reduceIte]
    intro p hp hdiv
    obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
    exact ((D.groups x).prime g p hpg).not_dvd_one hdiv


end Erdos821.S56Core
