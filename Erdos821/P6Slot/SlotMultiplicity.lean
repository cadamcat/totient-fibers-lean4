import Erdos821.S56.Tasks
import Erdos821.S56.SlotSplitTasks

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Slot
open Erdos821.Blueprint

abbrev PureLists (D : BandData) (x : ℝ) (S : Finset (D.Slot x)) :=
  (s : S) → {p : ℕ // p ∈ D.band x s.val.1.val}

def pureListProduct (D : BandData) (x : ℝ) (S : Finset (D.Slot x))
    (z : PureLists D x S) : ℕ := ∏ s : S, (z s).val

/-- The same prime multiplicity/permutation argument needed for aQ also
bounds every partial pure-prime coefficient after a fixed allocation pattern.
The subset S carries labelled slots and may omit any number from each band.
This is §5, typeii-separated-coefficients, a_e and c_r. -/
def PureSlotMultiplicityTask : Prop :=
  ∀ D : BandData, D.Valid → ∀ᶠ x : ℝ in atTop,
    ∀ (S : Finset (D.Slot x)) (v : ℕ),
      ((Finset.univ.filter (fun z : PureLists D x S => pureListProduct D x S z = v)).card : ℝ) ≤
        (D.r₀.factorial : ℝ) ^ (D.last x + 1)

/-- Transporting a multiset occurrence along multiset equality preserves its value. -/
lemma coe_cast_multiset {α : Type*} [DecidableEq α] (m n : Multiset α) (h : m = n)
    (x : Multiset.ToType m) :
    ((Equiv.cast (congrArg Multiset.ToType h) x : Multiset.ToType n) : α) = (x : α) := by
  cases h
  rfl

/-- Equal finite multisets of tuple values are related by a permutation of positions. -/
lemma exists_perm_of_map_univ_eq {α : Type*} [DecidableEq α] {n : ℕ}
    {f g : Fin n → α}
    (h : (Finset.univ.val.map f) = (Finset.univ.val.map g)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, g i = f (σ i) := by
  classical
  let s : Multiset (Fin n) := Finset.univ.val
  let e₀ : Fin n ≃ s := {
    toFun := fun i => ⟨i, ⟨0, by simp [s]⟩⟩
    invFun := fun i => i.1
    left_inv := by intro i; rfl
    right_inv := by
      intro i
      cases i with
      | mk a ha =>
        dsimp
        have hc : Multiset.count a s = 1 := by simp [s]
        have hha : ha = ⟨0, by simp [hc]⟩ := by
          apply Fin.ext
          have hlt : (ha.val : ℕ) < 1 := by simpa [hc] using ha.isLt
          omega
        rw [hha]
        }
  have h' : s.map f = s.map g := h
  let ef : s ≃ s.map f := Multiset.mapEquiv s f
  let eg : s ≃ s.map g := Multiset.mapEquiv s g
  let castfg : s.map f ≃ s.map g := Equiv.cast (congrArg Multiset.ToType h')
  let e : s ≃ s := ef.trans (castfg.trans eg.symm)
  let ρ : Equiv.Perm (Fin n) := e₀.trans (e.trans e₀.symm)
  have hρ : ∀ i, g (ρ i) = f i := by
    intro i
    have heval : eg (e (e₀ i)) = castfg (ef (e₀ i)) := by
      simp [e, Equiv.trans_apply]
    have hcoe := congrArg (fun x : s.map g => (x : α)) heval
    have hrel : g ((e (e₀ i) : s) : Fin n) = f i := by
      calc
        g ((e (e₀ i) : s) : Fin n) = ((eg (e (e₀ i)) : s.map g) : α) := by
          simp [eg, Multiset.mapEquiv_apply]
        _ = ((castfg (ef (e₀ i)) : s.map g) : α) := hcoe
        _ = ((ef (e₀ i) : s.map f) : α) := coe_cast_multiset _ _ h' _
        _ = f i := by
          rw [Multiset.mapEquiv_apply]
          change f i = f i
          rfl
    change g (e₀.symm (e (e₀ i))) = f i
    change g ((e (e₀ i) : s).1) = f i
    exact hrel
  refine ⟨ρ.symm, ?_⟩
  intro i
  simpa using hρ (ρ.symm i)

/-- Prime tuples with equal products have the same value multiset. -/
lemma map_univ_eq_of_prime_prod_eq {n : ℕ} {f g : Fin n → ℕ}
    (hf : ∀ i, Nat.Prime (f i)) (hg : ∀ i, Nat.Prime (g i))
    (hprod : (∏ i, f i) = (∏ i, g i)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  classical
  apply Multiset.ext.2
  intro p
  have hfac : (∏ i, f i).factorization p = (∏ i, g i).factorization p :=
    congrArg (fun n : ℕ => n.factorization p) hprod
  have hfprod : (∏ i, f i).factorization = ∑ i, (f i).factorization := by
    simpa using (Nat.factorization_prod (S := Finset.univ) (g := f) (by
      intro i hi
      exact (hf i).ne_zero))
  have hgprod : (∏ i, g i).factorization = ∑ i, (g i).factorization := by
    simpa using (Nat.factorization_prod (S := Finset.univ) (g := g) (by
      intro i hi
      exact (hg i).ne_zero))
  rw [hfprod, hgprod] at hfac
  have hcf : (Finset.univ.val.map f).count p =
      ∑ i : Fin n, if p = f i then 1 else 0 := by
    rw [Multiset.count_map]
    change (Finset.univ.filter (fun i : Fin n => p = f i)).card = _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hcg : (Finset.univ.val.map g).count p =
      ∑ i : Fin n, if p = g i then 1 else 0 := by
    rw [Multiset.count_map]
    change (Finset.univ.filter (fun i : Fin n => p = g i)).card = _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hfac' : ∑ i : Fin n, (f i).factorization p =
      ∑ i : Fin n, (g i).factorization p := by
    simpa only [Finsupp.finsetSum_apply] using hfac
  calc
    (Finset.univ.val.map f).count p = ∑ i : Fin n, if p = f i then 1 else 0 := hcf
    _ = ∑ i : Fin n, (f i).factorization p := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.Prime.factorization (hf i)]
      simp [Finsupp.single_apply, eq_comm]
    _ = ∑ i : Fin n, (g i).factorization p := hfac'
    _ = ∑ i : Fin n, if p = g i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.Prime.factorization (hg i)]
      simp [Finsupp.single_apply, eq_comm]
    _ = (Finset.univ.val.map g).count p := hcg.symm

lemma count_map_univ_eq_card_filter {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (p : α) :
    (Finset.univ.val.map f).count p = (Finset.univ.filter (fun i => f i = p)).card := by
  rw [Multiset.count_map]
  congr 1
  ext i
  simp [eq_comm]

/-- The same count formula when the factors are primes, with some unit factors. -/
lemma factorization_prod_card_filter_one_or_prime {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ)
    (hf : ∀ i ∈ s, f i = 1 ∨ Nat.Prime (f i)) (p : ℕ) (hp : Nat.Prime p) :
    (∏ i ∈ s, f i).factorization p = (s.filter (fun i => f i = p)).card := by
  have hp' : (∏ i ∈ s, f i).factorization = ∑ i ∈ s, (f i).factorization := by
    apply Nat.factorization_prod
    intro i hi
    rcases hf i hi with h | h
    · rw [h]
      exact one_ne_zero
    · exact h.ne_zero
  calc
    (∏ i ∈ s, f i).factorization p = ∑ i ∈ s, if p = f i then 1 else 0 := by
      rw [hp', Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rcases hf i hi with h1 | hq
      · rw [h1, Nat.factorization_one]
        simp [hp.ne_one]
      · rw [Nat.Prime.factorization hq]
        simp [Finsupp.single_apply, eq_comm]
    _ = (s.filter (fun i => f i = p)).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      simp [eq_comm]

lemma map_univ_eq_of_one_or_prime_prod_eq {n : ℕ} {f g : Fin n → ℕ}
    (hf : ∀ i, f i = 1 ∨ Nat.Prime (f i))
    (hg : ∀ i, g i = 1 ∨ Nat.Prime (g i))
    (hprod : (∏ i, f i) = (∏ i, g i))
    (hones : (Finset.univ.filter (fun i : Fin n => f i = 1)).card =
      (Finset.univ.filter (fun i : Fin n => g i = 1)).card) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  classical
  apply Multiset.ext.2
  intro p
  have hcf := count_map_univ_eq_card_filter f p
  have hcg := count_map_univ_eq_card_filter g p
  by_cases hp : Nat.Prime p
  · have hprodF : (∏ i, f i).factorization p =
        (Finset.univ.filter (fun i : Fin n => f i = p)).card :=
      factorization_prod_card_filter_one_or_prime Finset.univ f
        (by intro i hi; exact hf i) p hp
    have hprodG : (∏ i, g i).factorization p =
        (Finset.univ.filter (fun i : Fin n => g i = p)).card :=
      factorization_prod_card_filter_one_or_prime Finset.univ g
        (by intro i hi; exact hg i) p hp
    calc
      (Finset.univ.val.map f).count p = (Finset.univ.filter (fun i => f i = p)).card := hcf
      _ = (∏ i, f i).factorization p := hprodF.symm
      _ = (∏ i, g i).factorization p := congrArg (fun n : ℕ => n.factorization p) hprod
      _ = (Finset.univ.filter (fun i => g i = p)).card := hprodG
      _ = (Finset.univ.val.map g).count p := hcg.symm
  · by_cases hp1 : p = 1
    · subst p
      calc
        (Finset.univ.val.map f).count 1 =
            (Finset.univ.filter (fun i : Fin n => f i = 1)).card := hcf
        _ = (Finset.univ.filter (fun i : Fin n => g i = 1)).card := hones
        _ = (Finset.univ.val.map g).count 1 := hcg.symm
    · have hzeroF : Finset.univ.filter (fun i : Fin n => f i = p) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
        constructor
        · intro hEq
          rcases hf i with hone | hprime
          · exact hp1 (hEq.symm.trans hone)
          · exact hp (hEq ▸ hprime)
        · intro hfalse
          exact False.elim hfalse
      have hzeroG : Finset.univ.filter (fun i : Fin n => g i = p) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
        constructor
        · intro hEq
          rcases hg i with hone | hprime
          · exact hp1 (hEq.symm.trans hone)
          · exact hp (hEq ▸ hprime)
        · intro hfalse
          exact False.elim hfalse
      rw [hcf, hcg, hzeroF, hzeroG]

/-- In a product of primes, the exponent of `p` is the number of factors equal to `p`. -/
lemma factorization_prod_card_filter {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (hf : ∀ i ∈ s, Nat.Prime (f i)) (p : ℕ) :
    (∏ i ∈ s, f i).factorization p = (s.filter (fun i => f i = p)).card := by
  have hp : (∏ i ∈ s, f i).factorization = ∑ i ∈ s, (f i).factorization := by
    exact Nat.factorization_prod (S := s) (g := f) (fun i hi => (hf i hi).ne_zero)
  calc
    (∏ i ∈ s, f i).factorization p = ∑ i ∈ s, if p = f i then 1 else 0 := by
      rw [hp, Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.Prime.factorization (hf i hi)]
      simp [Finsupp.single_apply, eq_comm]
    _ = (s.filter (fun i => f i = p)).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      simp [eq_comm]

def exceptionSlot (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) : D.Slot x :=
  (⟨jstar, Nat.lt_succ_of_le hj⟩, ⟨0, hr⟩)

lemma slot_eq_exceptionSlot_iff (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (s : D.Slot x) :
    s = exceptionSlot D x jstar hj hr ↔ s.1.val = jstar ∧ s.2.val = 0 := by
  constructor
  · intro h
    exact ⟨congrArg (fun t : D.Slot x => t.1.val) h,
      congrArg (fun t : D.Slot x => t.2.val) h⟩
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext
    · exact Fin.ext h₁
    · exact Fin.ext h₂

def slotPureValue (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀)
    (z : D.Lists x jstar) (s : D.Slot x) : ℕ :=
  if s = exceptionSlot D x jstar hj hr then 1 else (z s).val

def bandPureValue (D : BandData) (x : ℝ) (jstar : ℕ)
    (z : D.Lists x jstar) (j : Fin (D.last x + 1)) (k : Fin D.r₀) : ℕ :=
  if j.val = jstar ∧ k.val = 0 then 1 else (z (j, k)).val

def bandPureProduct (D : BandData) (x : ℝ) (jstar : ℕ)
    (z : D.Lists x jstar) (j : Fin (D.last x + 1)) : ℕ :=
  ∏ k : Fin D.r₀, bandPureValue D x jstar z j k

lemma slot_value_prime (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z : D.Lists x jstar) (s : D.Slot x)
    (hs : s ≠ exceptionSlot D x jstar hj hr) :
    (z s).val ∈ D.band x s.1.val ∧ Nat.Prime (z s).val := by
  have hbranch : ¬(s.1.val = jstar ∧ s.2.val = 0) := by
    intro h
    exact hs ((slot_eq_exceptionSlot_iff D x jstar hj hr s).2 h)
  have hv : (z s).val ∈ D.slotValues x jstar s := (z s).property
  simp only [BandData.slotValues, if_neg hbranch] at hv
  refine ⟨hv, ?_⟩
  have hv' : (z s).val ∈
      (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x s.1.val)⌉₊
        ⌊Real.exp (D.c₂ * D.scale x s.1.val)⌋₊).filter Nat.Prime := by
    simpa [BandData.band] using hv
  exact (Finset.mem_filter.mp hv').2

lemma slot_value_pos (D : BandData) (x : ℝ) (jstar : ℕ)
    (z : D.Lists x jstar) (s : D.Slot x) : 0 < (z s).val := by
  have hv : (z s).val ∈ D.slotValues x jstar s := (z s).property
  by_cases he : s.1.val = jstar ∧ s.2.val = 0
  · simp [BandData.slotValues, he] at hv
    have hvalR : (0 : ℝ) < (z s).val :=
      lt_of_lt_of_le (Real.exp_pos _) hv.1.1
    exact_mod_cast hvalR
  · simp [BandData.slotValues, he] at hv
    have hv' : (z s).val ∈
        (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x s.1.val)⌉₊
          ⌊Real.exp (D.c₂ * D.scale x s.1.val)⌋₊).filter Nat.Prime := by
      simpa [BandData.band] using hv
    exact (Finset.mem_filter.mp hv').2.pos

lemma bandPureValue_one_or_prime (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z : D.Lists x jstar)
    (j : Fin (D.last x + 1)) (k : Fin D.r₀) :
    bandPureValue D x jstar z j k = 1 ∨
      Nat.Prime (bandPureValue D x jstar z j k) ∧
        bandPureValue D x jstar z j k ∈ D.band x j.val := by
  by_cases he : j.val = jstar ∧ k.val = 0
  · left
    simp [bandPureValue, he]
  · right
    have hs : (j, k) ≠ exceptionSlot D x jstar hj hr := by
      intro h
      exact he ((slot_eq_exceptionSlot_iff D x jstar hj hr (j, k)).1 h)
    obtain ⟨hmem, hp⟩ := slot_value_prime D x jstar hj hr z (j, k) hs
    exact ⟨by simpa [bandPureValue, he] using hp,
      by simpa [bandPureValue, he] using hmem⟩

def pureProduct (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z : D.Lists x jstar) : ℕ :=
  ∏ s : D.Slot x, slotPureValue D x jstar hj hr z s

lemma pureProduct_eq_bandProducts (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z : D.Lists x jstar) :
    pureProduct D x jstar hj hr z =
      ∏ j : Fin (D.last x + 1), bandPureProduct D x jstar z j := by
  classical
  have huniv : (Finset.univ : Finset (Fin (D.last x + 1) × Fin D.r₀)) =
      (Finset.univ : Finset (Fin (D.last x + 1))) ×ˢ
        (Finset.univ : Finset (Fin D.r₀)) := by
    ext s
    simp
  unfold pureProduct bandPureProduct slotPureValue bandPureValue
  rw [huniv, Finset.prod_product]
  apply Finset.prod_congr rfl
  intro j hj'
  apply Finset.prod_congr rfl
  intro k hk'
  by_cases he : j.val = jstar ∧ k.val = 0
  · simp [slot_eq_exceptionSlot_iff D x jstar hj hr (j, k), he]
  · simp [slot_eq_exceptionSlot_iff D x jstar hj hr (j, k), he]

lemma listProduct_eq_pureProduct_mul (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z : D.Lists x jstar) :
    D.listProduct z = pureProduct D x jstar hj hr z * (z (exceptionSlot D x jstar hj hr)).val := by
  classical
  let e := exceptionSlot D x jstar hj hr
  have he : e ∈ (Finset.univ : Finset (D.Slot x)) := Finset.mem_univ _
  have hpure : pureProduct D x jstar hj hr z =
      ∏ s ∈ (Finset.univ : Finset (D.Slot x)).erase e, (z s).val := by
    unfold pureProduct slotPureValue
    rw [← Finset.prod_erase (s := Finset.univ) (a := e)
      (f := fun s : D.Slot x => if s = e then 1 else (z s).val) (by simp)]
    apply Finset.prod_congr rfl
    intro s hs
    simp [Finset.mem_erase.mp hs]
  calc
    D.listProduct z =
        (∏ s ∈ (Finset.univ : Finset (D.Slot x)).erase e, (z s).val) * (z e).val := by
      simpa [BandData.listProduct] using
        (Finset.prod_erase_mul (Finset.univ : Finset (D.Slot x))
          (fun s => (z s).val) he).symm
    _ = pureProduct D x jstar hj hr z * (z e).val := by rw [← hpure]

lemma pureProduct_eq_of_listProduct_eq (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z z' : D.Lists x jstar)
    (hprod : D.listProduct z = D.listProduct z')
    (he : (z (exceptionSlot D x jstar hj hr)).val =
      (z' (exceptionSlot D x jstar hj hr)).val) :
    pureProduct D x jstar hj hr z = pureProduct D x jstar hj hr z' := by
  have hz := listProduct_eq_pureProduct_mul D x jstar hj hr z
  have hz' := listProduct_eq_pureProduct_mul D x jstar hj hr z'
  rw [hz, hz'] at hprod
  rw [he] at hprod
  exact Nat.mul_right_cancel (slot_value_pos D x jstar z' (exceptionSlot D x jstar hj hr)) hprod

lemma bandPureProduct_ne_zero (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z : D.Lists x jstar)
    (j : Fin (D.last x + 1)) : bandPureProduct D x jstar z j ≠ 0 := by
  unfold bandPureProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  rcases bandPureValue_one_or_prime D x jstar hj hr z j k with he | ⟨hp, _⟩
  · rw [he]
    exact one_ne_zero
  · exact hp.ne_zero

lemma bandPureFactorization_zero_of_not_mem (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z : D.Lists x jstar)
    (j : Fin (D.last x + 1)) (p : ℕ) (hp : Nat.Prime p)
    (hnot : p ∉ D.band x j.val) :
    (bandPureProduct D x jstar z j).factorization p = 0 := by
  unfold bandPureProduct
  rw [factorization_prod_card_filter_one_or_prime (Finset.univ : Finset (Fin D.r₀))
    (bandPureValue D x jstar z j)
    (by
      intro k hk
      rcases bandPureValue_one_or_prime D x jstar hj hr z j k with hone | ⟨hprime, _⟩
      · exact Or.inl hone
      · exact Or.inr hprime) p hp]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨_, heq⟩
  rcases bandPureValue_one_or_prime D x jstar hj hr z j k with hone | ⟨_, hmem⟩
  · exact hp.ne_one (heq.symm.trans hone)
  · exact hnot (heq ▸ hmem)

lemma bandPureFactorization_formula (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀) (z : D.Lists x jstar) (p : ℕ) :
    (pureProduct D x jstar hj hr z).factorization p =
      ∑ j : Fin (D.last x + 1), (bandPureProduct D x jstar z j).factorization p := by
  have hfac : (∏ j : Fin (D.last x + 1), bandPureProduct D x jstar z j).factorization =
      ∑ j : Fin (D.last x + 1), (bandPureProduct D x jstar z j).factorization := by
    apply Nat.factorization_prod
    intro j hj'
    exact bandPureProduct_ne_zero D x jstar hj hr z j
  calc
    (pureProduct D x jstar hj hr z).factorization p =
        (∏ j : Fin (D.last x + 1), bandPureProduct D x jstar z j).factorization p := by
      rw [pureProduct_eq_bandProducts D x jstar hj hr z]
    _ = ∑ j : Fin (D.last x + 1), (bandPureProduct D x jstar z j).factorization p := by
      rw [hfac, Finsupp.finsetSum_apply]

lemma bandPureProduct_eq_of_pureProduct_eq (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀)
    (hdisj : ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
      Disjoint (D.band x i) (D.band x j))
    (z z' : D.Lists x jstar) (hprod : pureProduct D x jstar hj hr z =
      pureProduct D x jstar hj hr z') (j : Fin (D.last x + 1)) :
    bandPureProduct D x jstar z j = bandPureProduct D x jstar z' j := by
  apply Nat.factorization_inj (bandPureProduct_ne_zero D x jstar hj hr z j)
    (bandPureProduct_ne_zero D x jstar hj hr z' j)
  ext p
  have hglobal : (pureProduct D x jstar hj hr z).factorization p =
      (pureProduct D x jstar hj hr z').factorization p :=
    congrArg (fun n : ℕ => n.factorization p) hprod
  by_cases hp : Nat.Prime p
  · by_cases hmem : p ∈ D.band x j.val
    · have hsum (w : D.Lists x jstar) :
        (∑ i : Fin (D.last x + 1), (bandPureProduct D x jstar w i).factorization p) =
          (bandPureProduct D x jstar w j).factorization p := by
        exact Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun i hi hne => by
          have hne' : i.val ≠ j.val := by
            intro heq
            exact hne (Fin.ext heq)
          have hji : Disjoint (D.band x i.val) (D.band x j.val) :=
            hdisj i.val (Nat.le_of_lt_succ i.isLt) j.val (Nat.le_of_lt_succ j.isLt) hne'
          apply bandPureFactorization_zero_of_not_mem D x jstar hj hr w i p hp
          intro hpi
          exact (Finset.disjoint_left.mp hji) hpi hmem)
      rw [bandPureFactorization_formula D x jstar hj hr z p,
        bandPureFactorization_formula D x jstar hj hr z' p, hsum z, hsum z'] at hglobal
      exact hglobal
    · rw [bandPureFactorization_zero_of_not_mem D x jstar hj hr z j p hp hmem,
        bandPureFactorization_zero_of_not_mem D x jstar hj hr z' j p hp hmem]
  · simp [Nat.factorization_eq_zero_of_not_prime, hp]

lemma bandValues_multiset_eq (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀)
    (hdisj : ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
      Disjoint (D.band x i) (D.band x j))
    (z z' : D.Lists x jstar)
    (hproduct : D.listProduct z = D.listProduct z')
    (he : (z (exceptionSlot D x jstar hj hr)).val =
      (z' (exceptionSlot D x jstar hj hr)).val)
    (j : Fin (D.last x + 1)) :
    Finset.univ.val.map (fun k : Fin D.r₀ => (z (j, k)).val) =
      Finset.univ.val.map (fun k : Fin D.r₀ => (z' (j, k)).val) := by
  classical
  have hpure := pureProduct_eq_of_listProduct_eq D x jstar hj hr z z' hproduct he
  have hbandProduct := bandPureProduct_eq_of_pureProduct_eq D x jstar hj hr hdisj
    z z' hpure j
  have honeSets :
      (Finset.univ : Finset (Fin D.r₀)).filter
        (fun k => bandPureValue D x jstar z j k = 1) =
      (Finset.univ : Finset (Fin D.r₀)).filter
        (fun k => bandPureValue D x jstar z' j k = 1) := by
    ext k
    by_cases hk : j.val = jstar ∧ k.val = 0
    · simp [bandPureValue, hk]
    · have hs : (j, k) ≠ exceptionSlot D x jstar hj hr := by
        intro h
        exact hk ((slot_eq_exceptionSlot_iff D x jstar hj hr (j, k)).1 h)
      obtain ⟨_, hp⟩ := slot_value_prime D x jstar hj hr z (j, k) hs
      obtain ⟨_, hp'⟩ := slot_value_prime D x jstar hj hr z' (j, k) hs
      simp [bandPureValue, hk, hp.ne_one, hp'.ne_one]
  have hones := congrArg Finset.card honeSets
  have hpureMultiset := map_univ_eq_of_one_or_prime_prod_eq
    (f := bandPureValue D x jstar z j) (g := bandPureValue D x jstar z' j)
    (by
      intro k
      rcases bandPureValue_one_or_prime D x jstar hj hr z j k with hone | ⟨hp, _⟩
      · exact Or.inl hone
      · exact Or.inr hp)
    (by
      intro k
      rcases bandPureValue_one_or_prime D x jstar hj hr z' j k with hone | ⟨hp, _⟩
      · exact Or.inl hone
      · exact Or.inr hp)
    hbandProduct hones
  let repair : ℕ → ℕ := fun n => if n = 1 then (z (exceptionSlot D x jstar hj hr)).val else n
  have hrepairZ : ∀ k : Fin D.r₀,
      repair (bandPureValue D x jstar z j k) = (z (j, k)).val := by
    intro k
    by_cases hk : j.val = jstar ∧ k.val = 0
    · have hslot := (slot_eq_exceptionSlot_iff D x jstar hj hr (j, k)).2 hk
      simp [repair, bandPureValue, hk]
      rw [← hslot]
    · have hs : (j, k) ≠ exceptionSlot D x jstar hj hr := by
        intro h
        exact hk ((slot_eq_exceptionSlot_iff D x jstar hj hr (j, k)).1 h)
      obtain ⟨_, hp⟩ := slot_value_prime D x jstar hj hr z (j, k) hs
      simp [repair, bandPureValue, hk, hp.ne_one]
  have hrepairZ' : ∀ k : Fin D.r₀,
      repair (bandPureValue D x jstar z' j k) = (z' (j, k)).val := by
    intro k
    by_cases hk : j.val = jstar ∧ k.val = 0
    · have hslot := (slot_eq_exceptionSlot_iff D x jstar hj hr (j, k)).2 hk
      simp [repair, bandPureValue, hk]
      rw [hslot, he]
    · have hs : (j, k) ≠ exceptionSlot D x jstar hj hr := by
        intro h
        exact hk ((slot_eq_exceptionSlot_iff D x jstar hj hr (j, k)).1 h)
      obtain ⟨_, hp⟩ := slot_value_prime D x jstar hj hr z' (j, k) hs
      simp [repair, bandPureValue, hk, hp.ne_one]
  have hmapRepair (w : D.Lists x jstar) (hrepair : ∀ k,
      repair (bandPureValue D x jstar w j k) = (w (j, k)).val) :
      Finset.univ.val.map (fun k : Fin D.r₀ => (w (j, k)).val) =
        (Finset.univ.val.map (fun k : Fin D.r₀ => bandPureValue D x jstar w j k)).map repair := by
    calc
      Finset.univ.val.map (fun k : Fin D.r₀ => (w (j, k)).val) =
          Finset.univ.val.map (repair ∘ fun k : Fin D.r₀ => bandPureValue D x jstar w j k) := by
        apply Multiset.map_congr rfl
        intro k hk
        exact (hrepair k).symm
      _ = (Finset.univ.val.map (fun k : Fin D.r₀ => bandPureValue D x jstar w j k)).map repair := by
        rw [Multiset.map_map]
  calc
    Finset.univ.val.map (fun k : Fin D.r₀ => (z (j, k)).val) =
        (Finset.univ.val.map (fun k : Fin D.r₀ => bandPureValue D x jstar z j k)).map repair :=
      hmapRepair z hrepairZ
    _ = (Finset.univ.val.map (fun k : Fin D.r₀ => bandPureValue D x jstar z' j k)).map repair :=
      congrArg (Multiset.map repair) hpureMultiset
    _ = Finset.univ.val.map (fun k : Fin D.r₀ => (z' (j, k)).val) :=
      (hmapRepair z' hrepairZ').symm

def bandTuple (D : BandData) (x : ℝ) (jstar : ℕ)
    (z : D.Lists x jstar) (j : Fin (D.last x + 1)) : Fin D.r₀ → ℕ :=
  fun k => (z (j, k)).val

lemma list_fiber_card_le_factorial_pow (D : BandData) (x : ℝ) (jstar v e : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀)
    (hdisj : ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
      Disjoint (D.band x i) (D.band x j)) :
    Fintype.card {z : D.Lists x jstar //
      D.listProduct z = v ∧ (z (exceptionSlot D x jstar hj hr)).val = e} ≤
        (D.r₀.factorial) ^ (D.last x + 1) := by
  classical
  let Fiber := {z : D.Lists x jstar //
    D.listProduct z = v ∧ (z (exceptionSlot D x jstar hj hr)).val = e}
  by_cases hne : Nonempty Fiber
  · let base : Fiber := Classical.choice hne
    let encode : Fiber → (∀ j : Fin (D.last x + 1), Equiv.Perm (Fin D.r₀)) := fun w j =>
      Classical.choose (exists_perm_of_map_univ_eq
        (f := bandTuple D x jstar base.val j) (g := bandTuple D x jstar w.val j)
        (bandValues_multiset_eq D x jstar hj hr hdisj base.val w.val
          (base.property.1.trans w.property.1.symm)
          (base.property.2.trans w.property.2.symm) j))
    have hspec (w : Fiber) (j : Fin (D.last x + 1)) (k : Fin D.r₀) :
        bandTuple D x jstar w.val j k = bandTuple D x jstar base.val j (encode w j k) :=
      Classical.choose_spec (exists_perm_of_map_univ_eq
        (f := bandTuple D x jstar base.val j) (g := bandTuple D x jstar w.val j)
        (bandValues_multiset_eq D x jstar hj hr hdisj base.val w.val
          (base.property.1.trans w.property.1.symm)
          (base.property.2.trans w.property.2.symm) j)) k
    have hencode : Function.Injective encode := by
      intro w w' h
      apply Subtype.ext
      funext s
      rcases s with ⟨j, k⟩
      apply Subtype.ext
      have hperm : encode w j k = encode w' j k := by
        exact congrArg (fun σ : Equiv.Perm (Fin D.r₀) => σ k) (congrFun h j)
      calc
        (w.val (j, k)).val = (base.val (j, encode w j k)).val := hspec w j k
        _ = (base.val (j, encode w' j k)).val := by rw [hperm]
        _ = (w'.val (j, k)).val := (hspec w' j k).symm
    have hcardPi : Fintype.card (∀ j : Fin (D.last x + 1), Equiv.Perm (Fin D.r₀)) =
        (D.r₀.factorial) ^ (D.last x + 1) := by
      simp [Fintype.card_pi, Fintype.card_perm, Fintype.card_fin]
    calc
      Fintype.card Fiber ≤
          Fintype.card (∀ j : Fin (D.last x + 1), Equiv.Perm (Fin D.r₀)) :=
        Fintype.card_le_of_injective encode hencode
      _ = (D.r₀.factorial) ^ (D.last x + 1) := hcardPi
  · letI : IsEmpty Fiber := not_nonempty_iff.mp hne
    simp [Fiber]

lemma list_product_pos (D : BandData) (x : ℝ) (jstar : ℕ)
    (z : D.Lists x jstar) : 0 < D.listProduct z := by
  unfold BandData.listProduct
  apply Finset.prod_pos
  intro s hs
  exact slot_value_pos D x jstar z s

lemma list_card_le_divisor_card_mul_factorial (D : BandData) (x : ℝ) (jstar v : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀)
    (hdisj : ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
      Disjoint (D.band x i) (D.band x j)) :
    (Finset.univ.filter (fun z : D.Lists x jstar => D.listProduct z = v)).card ≤
      v.divisors.card * (D.r₀.factorial) ^ (D.last x + 1) := by
  classical
  let S : Finset (D.Lists x jstar) :=
    Finset.univ.filter (fun z => D.listProduct z = v)
  let exceptionalValue : D.Lists x jstar → ℕ :=
    fun z => (z (exceptionSlot D x jstar hj hr)).val
  let F : ℕ := (D.r₀.factorial) ^ (D.last x + 1)
  have hmaps : ∀ z ∈ S, exceptionalValue z ∈ v.divisors := by
    intro z hz
    have hprod : D.listProduct z = v := (Finset.mem_filter.mp hz).2
    have hvpos : 0 < v := by rw [← hprod]; exact list_product_pos D x jstar z
    have hediv : exceptionalValue z ∣ v := by
      refine ⟨pureProduct D x jstar hj hr z, ?_⟩
      calc
        v = D.listProduct z := hprod.symm
        _ = pureProduct D x jstar hj hr z * exceptionalValue z :=
          listProduct_eq_pureProduct_mul D x jstar hj hr z
        _ = exceptionalValue z * pureProduct D x jstar hj hr z := Nat.mul_comm _ _
    exact Nat.mem_divisors.mpr ⟨hediv, hvpos.ne'⟩
  have hfibers : ∀ e ∈ v.divisors,
      (S.filter (fun z => exceptionalValue z = e)).card ≤ F := by
    intro e he
    let Fs : Finset (D.Lists x jstar) := S.filter (fun z => exceptionalValue z = e)
    let Fiber := {z : D.Lists x jstar //
      D.listProduct z = v ∧ exceptionalValue z = e}
    have hcard : Fintype.card Fiber = Fs.card := by
      apply Fintype.card_of_subtype Fs
      intro z
      simp [Fs, S, and_comm]
    calc
      (S.filter (fun z => exceptionalValue z = e)).card = Fs.card := by rfl
      _ = Fintype.card Fiber := hcard.symm
      _ ≤ F := list_fiber_card_le_factorial_pow D x jstar v e hj hr hdisj
  calc
    S.card ≤ F * v.divisors.card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps F hfibers
    _ = v.divisors.card * F := Nat.mul_comm _ _

theorem slotMultiplicityTask_proof : Erdos821.S56Core.SlotMultiplicityTask := by
  intro D hD jstar
  rcases hD with ⟨hr0, hc1, hc12, hs', hratio, hdelta, hroom, hlast,
    cmin, cmax, hcmin, hcmax, hgood⟩
  have hr : 0 < D.r₀ := Nat.succ_le_iff.mp hr0
  have hlastEvent : ∀ᶠ x : ℝ in atTop, jstar ≤ D.last x :=
    (Filter.tendsto_atTop.1 hlast) jstar
  have hdisjEvent : ∀ᶠ x : ℝ in atTop,
      ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
        Disjoint (D.band x i) (D.band x j) := by
    filter_upwards [hgood] with x hx
    rcases hx with ⟨_, _, _, hdisj, _⟩
    exact hdisj
  filter_upwards [hlastEvent, hdisjEvent] with x hxlast hxdisj
  intro v
  have hcount := list_card_le_divisor_card_mul_factorial D x jstar v hxlast hr hxdisj
  let S : Finset (D.Lists x jstar) :=
    Finset.univ.filter (fun z => D.listProduct z = v)
  have hcountR : (S.card : ℝ) ≤
      (v.divisors.card : ℝ) * (D.r₀.factorial : ℝ) ^ (D.last x + 1) := by
    exact_mod_cast hcount
  let d : ℝ := (D.r₀.factorial : ℝ) ^ (D.last x + 1)
  have hd : 0 < d := by positivity
  have hmul : d⁻¹ * (S.card : ℝ) ≤ d⁻¹ * ((v.divisors.card : ℝ) * d) :=
    mul_le_mul_of_nonneg_left hcountR (inv_nonneg.mpr hd.le)
  have hrhs : d⁻¹ * ((v.divisors.card : ℝ) * d) = (v.divisors.card : ℝ) := by
    field_simp [hd.ne']
  calc
    D.aQ x jstar v = d⁻¹ * (S.card : ℝ) := by
      simp [BandData.aQ, S, d]
    _ ≤ d⁻¹ * ((v.divisors.card : ℝ) * d) := hmul
    _ = (v.divisors.card : ℝ) := hrhs

def pureBandValue (D : BandData) (x : ℝ) (S : Finset (D.Slot x))
    (z : PureLists D x S) (j : Fin (D.last x + 1)) (k : Fin D.r₀) : ℕ :=
  if h : (j, k) ∈ S then (z ⟨(j, k), h⟩).val else 1

def pureBandProduct (D : BandData) (x : ℝ) (S : Finset (D.Slot x))
    (z : PureLists D x S) (j : Fin (D.last x + 1)) : ℕ :=
  ∏ k : Fin D.r₀, pureBandValue D x S z j k

lemma pureListProduct_eq_bandProducts (D : BandData) (x : ℝ)
    (S : Finset (D.Slot x)) (z : PureLists D x S) :
    pureListProduct D x S z =
      ∏ j : Fin (D.last x + 1), pureBandProduct D x S z j := by
  classical
  have hslots : pureListProduct D x S z =
      ∏ s : D.Slot x, pureBandValue D x S z s.1 s.2 := by
    simpa [pureListProduct, pureBandValue, Finset.univ_eq_attach] using
      (Finset.prod_attach_eq_prod_dite S (fun s => (z s).val))
  have huniv : (Finset.univ : Finset (D.Slot x)) =
      (Finset.univ : Finset (Fin (D.last x + 1))) ×ˢ
        (Finset.univ : Finset (Fin D.r₀)) := by
    ext s
    simp [BandData.Slot]
  calc
    pureListProduct D x S z =
        ∏ s ∈ (Finset.univ : Finset (D.Slot x)),
          pureBandValue D x S z s.1 s.2 := by simpa using hslots
    _ = ∏ j : Fin (D.last x + 1), ∏ k : Fin D.r₀,
          pureBandValue D x S z j k := by
      rw [huniv, Finset.prod_product]
    _ = ∏ j : Fin (D.last x + 1), pureBandProduct D x S z j := by
      rfl

lemma pureBandValue_one_or_prime (D : BandData) (x : ℝ)
    (S : Finset (D.Slot x)) (z : PureLists D x S)
    (j : Fin (D.last x + 1)) (k : Fin D.r₀) :
    pureBandValue D x S z j k = 1 ∨
      Nat.Prime (pureBandValue D x S z j k) ∧
        pureBandValue D x S z j k ∈ D.band x j.val := by
  classical
  by_cases hs : (j, k) ∈ S
  · right
    have hv : (z ⟨(j, k), hs⟩).val ∈ D.band x j.val := by
      simpa using (z ⟨(j, k), hs⟩).property
    have hv' : (z ⟨(j, k), hs⟩).val ∈
        (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x j.val)⌉₊
          ⌊Real.exp (D.c₂ * D.scale x j.val)⌋₊).filter Nat.Prime := by
      simpa [BandData.band] using hv
    have hp := (Finset.mem_filter.mp hv').2
    exact ⟨by simpa [pureBandValue, hs] using hp,
      by simpa [pureBandValue, hs] using hv⟩
  · left
    simp [pureBandValue, hs]

lemma pureBandProduct_ne_zero (D : BandData) (x : ℝ)
    (S : Finset (D.Slot x)) (z : PureLists D x S)
    (j : Fin (D.last x + 1)) : pureBandProduct D x S z j ≠ 0 := by
  unfold pureBandProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  rcases pureBandValue_one_or_prime D x S z j k with hone | ⟨hp, _⟩
  · rw [hone]
    exact one_ne_zero
  · exact hp.ne_zero

lemma pureBandFactorization_zero_of_not_mem (D : BandData) (x : ℝ)
    (S : Finset (D.Slot x)) (z : PureLists D x S)
    (j : Fin (D.last x + 1)) (p : ℕ) (hp : Nat.Prime p)
    (hnot : p ∉ D.band x j.val) :
    (pureBandProduct D x S z j).factorization p = 0 := by
  unfold pureBandProduct
  rw [factorization_prod_card_filter_one_or_prime (Finset.univ : Finset (Fin D.r₀))
    (pureBandValue D x S z j)
    (by
      intro k hk
      rcases pureBandValue_one_or_prime D x S z j k with hone | ⟨hprime, _⟩
      · exact Or.inl hone
      · exact Or.inr hprime) p hp]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨_, heq⟩
  rcases pureBandValue_one_or_prime D x S z j k with hone | ⟨_, hmem⟩
  · exact hp.ne_one (heq.symm.trans hone)
  · exact hnot (heq ▸ hmem)

lemma pureBandFactorization_formula (D : BandData) (x : ℝ)
    (S : Finset (D.Slot x)) (z : PureLists D x S) (p : ℕ) :
    (pureListProduct D x S z).factorization p =
      ∑ j : Fin (D.last x + 1), (pureBandProduct D x S z j).factorization p := by
  have hfac : (∏ j : Fin (D.last x + 1), pureBandProduct D x S z j).factorization =
      ∑ j : Fin (D.last x + 1), (pureBandProduct D x S z j).factorization := by
    apply Nat.factorization_prod
    intro j hj
    exact pureBandProduct_ne_zero D x S z j
  calc
    (pureListProduct D x S z).factorization p =
        (∏ j : Fin (D.last x + 1), pureBandProduct D x S z j).factorization p := by
      rw [pureListProduct_eq_bandProducts]
    _ = ∑ j : Fin (D.last x + 1), (pureBandProduct D x S z j).factorization p := by
      rw [hfac, Finsupp.finsetSum_apply]

lemma pureBandProduct_eq_of_pureListProduct_eq (D : BandData) (x : ℝ)
    (S : Finset (D.Slot x))
    (hdisj : ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
      Disjoint (D.band x i) (D.band x j))
    (z z' : PureLists D x S)
    (hprod : pureListProduct D x S z = pureListProduct D x S z')
    (j : Fin (D.last x + 1)) :
    pureBandProduct D x S z j = pureBandProduct D x S z' j := by
  apply Nat.factorization_inj (pureBandProduct_ne_zero D x S z j)
    (pureBandProduct_ne_zero D x S z' j)
  ext p
  have hglobal : (pureListProduct D x S z).factorization p =
      (pureListProduct D x S z').factorization p :=
    congrArg (fun n : ℕ => n.factorization p) hprod
  by_cases hp : Nat.Prime p
  · by_cases hmem : p ∈ D.band x j.val
    · have hsum (w : PureLists D x S) :
        (∑ i : Fin (D.last x + 1), (pureBandProduct D x S w i).factorization p) =
          (pureBandProduct D x S w j).factorization p := by
        exact Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun i hi hne => by
          have hne' : i.val ≠ j.val := by
            intro heq
            exact hne (Fin.ext heq)
          have hji : Disjoint (D.band x i.val) (D.band x j.val) :=
            hdisj i.val (Nat.le_of_lt_succ i.isLt) j.val (Nat.le_of_lt_succ j.isLt) hne'
          apply pureBandFactorization_zero_of_not_mem D x S w i p hp
          intro hpi
          exact (Finset.disjoint_left.mp hji) hpi hmem)
      rw [pureBandFactorization_formula D x S z p,
        pureBandFactorization_formula D x S z' p, hsum z, hsum z'] at hglobal
      exact hglobal
    · rw [pureBandFactorization_zero_of_not_mem D x S z j p hp hmem,
        pureBandFactorization_zero_of_not_mem D x S z' j p hp hmem]
  · simp [Nat.factorization_eq_zero_of_not_prime, hp]

lemma pureBandValues_multiset_eq (D : BandData) (x : ℝ)
    (S : Finset (D.Slot x))
    (hdisj : ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
      Disjoint (D.band x i) (D.band x j))
    (z z' : PureLists D x S)
    (hproduct : pureListProduct D x S z = pureListProduct D x S z')
    (j : Fin (D.last x + 1)) :
    Finset.univ.val.map (fun k : Fin D.r₀ => pureBandValue D x S z j k) =
      Finset.univ.val.map (fun k : Fin D.r₀ => pureBandValue D x S z' j k) := by
  classical
  have hbandProduct := pureBandProduct_eq_of_pureListProduct_eq D x S hdisj
    z z' hproduct j
  have honeSets :
      (Finset.univ : Finset (Fin D.r₀)).filter
        (fun k => pureBandValue D x S z j k = 1) =
      (Finset.univ : Finset (Fin D.r₀)).filter
        (fun k => pureBandValue D x S z' j k = 1) := by
    ext k
    by_cases hs : (j, k) ∈ S
    · have hp : Nat.Prime (z ⟨(j, k), hs⟩).val := by
        have hv : (z ⟨(j, k), hs⟩).val ∈ D.band x j.val := by
          simpa using (z ⟨(j, k), hs⟩).property
        have hv' : (z ⟨(j, k), hs⟩).val ∈
            (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x j.val)⌉₊
              ⌊Real.exp (D.c₂ * D.scale x j.val)⌋₊).filter Nat.Prime := by
          simpa [BandData.band] using hv
        exact (Finset.mem_filter.mp hv').2
      have hp' : Nat.Prime (z' ⟨(j, k), hs⟩).val := by
        have hv : (z' ⟨(j, k), hs⟩).val ∈ D.band x j.val := by
          simpa using (z' ⟨(j, k), hs⟩).property
        have hv' : (z' ⟨(j, k), hs⟩).val ∈
            (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x j.val)⌉₊
              ⌊Real.exp (D.c₂ * D.scale x j.val)⌋₊).filter Nat.Prime := by
          simpa [BandData.band] using hv
        exact (Finset.mem_filter.mp hv').2
      simp [pureBandValue, hs, hp.ne_one, hp'.ne_one]
    · simp [pureBandValue, hs]
  have hones := congrArg Finset.card honeSets
  exact map_univ_eq_of_one_or_prime_prod_eq
    (f := pureBandValue D x S z j) (g := pureBandValue D x S z' j)
    (by
      intro k
      rcases pureBandValue_one_or_prime D x S z j k with hone | ⟨hp, _⟩
      · exact Or.inl hone
      · exact Or.inr hp)
    (by
      intro k
      rcases pureBandValue_one_or_prime D x S z' j k with hone | ⟨hp, _⟩
      · exact Or.inl hone
      · exact Or.inr hp)
    hbandProduct hones

def pureBandTuple (D : BandData) (x : ℝ) (S : Finset (D.Slot x))
    (z : PureLists D x S) (j : Fin (D.last x + 1)) : Fin D.r₀ → ℕ :=
  fun k => pureBandValue D x S z j k

lemma pure_list_fiber_card_le_factorial_pow (D : BandData) (x : ℝ)
    (S : Finset (D.Slot x)) (v : ℕ)
    (hdisj : ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
      Disjoint (D.band x i) (D.band x j)) :
    Fintype.card {z : PureLists D x S // pureListProduct D x S z = v} ≤
      (D.r₀.factorial) ^ (D.last x + 1) := by
  classical
  let Fiber := {z : PureLists D x S // pureListProduct D x S z = v}
  change Fintype.card Fiber ≤ (D.r₀.factorial) ^ (D.last x + 1)
  by_cases hne : Nonempty Fiber
  · let base : Fiber := Classical.choice hne
    let encode : Fiber → (∀ j : Fin (D.last x + 1), Equiv.Perm (Fin D.r₀)) :=
      fun w j => Classical.choose (exists_perm_of_map_univ_eq
        (f := pureBandTuple D x S base.val j) (g := pureBandTuple D x S w.val j)
        (pureBandValues_multiset_eq D x S hdisj base.val w.val
          (base.property.trans w.property.symm) j))
    have hspec (w : Fiber) (j : Fin (D.last x + 1)) (k : Fin D.r₀) :
        pureBandTuple D x S w.val j k =
          pureBandTuple D x S base.val j (encode w j k) :=
      Classical.choose_spec (exists_perm_of_map_univ_eq
        (f := pureBandTuple D x S base.val j) (g := pureBandTuple D x S w.val j)
        (pureBandValues_multiset_eq D x S hdisj base.val w.val
          (base.property.trans w.property.symm) j)) k
    have hencode : Function.Injective encode := by
      intro w w' h
      apply Subtype.ext
      funext s
      rcases s with ⟨⟨j, k⟩, hs⟩
      apply Subtype.ext
      have hperm : encode w j k = encode w' j k :=
        congrArg (fun σ : Equiv.Perm (Fin D.r₀) => σ k) (congrFun h j)
      calc
        (w.val ⟨(j, k), hs⟩).val = pureBandValue D x S w.val j k := by
          simp [pureBandValue, hs]
        _ = pureBandValue D x S base.val j (encode w j k) := hspec w j k
        _ = pureBandValue D x S base.val j (encode w' j k) := by rw [hperm]
        _ = pureBandValue D x S w'.val j k := (hspec w' j k).symm
        _ = (w'.val ⟨(j, k), hs⟩).val := by simp [pureBandValue, hs]
    have hcardPi : Fintype.card (∀ j : Fin (D.last x + 1), Equiv.Perm (Fin D.r₀)) =
        (D.r₀.factorial) ^ (D.last x + 1) := by
      simp [Fintype.card_pi, Fintype.card_perm, Fintype.card_fin]
    calc
      Fintype.card Fiber ≤
          Fintype.card (∀ j : Fin (D.last x + 1), Equiv.Perm (Fin D.r₀)) :=
        Fintype.card_le_of_injective encode hencode
      _ = (D.r₀.factorial) ^ (D.last x + 1) := hcardPi
  · letI : IsEmpty Fiber := not_nonempty_iff.mp hne
    rw [Fintype.card_eq_zero_iff.mpr inferInstance]
    exact Nat.zero_le _

theorem pureSlotMultiplicityTask_proof : PureSlotMultiplicityTask := by
  intro D hD
  rcases hD with ⟨_, _, _, _, _, _, _, hlast, _, _, _, _, hgood⟩
  have hdisjEvent : ∀ᶠ x : ℝ in atTop,
      ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
        Disjoint (D.band x i) (D.band x j) := by
    filter_upwards [hgood] with x hx
    rcases hx with ⟨_, _, _, hdisj, _⟩
    exact hdisj
  filter_upwards [hdisjEvent] with x hxdisj
  intro S v
  let Fiber := {z : PureLists D x S // pureListProduct D x S z = v}
  have hcard : Fintype.card Fiber =
      (Finset.univ.filter (fun z : PureLists D x S => pureListProduct D x S z = v)).card := by
    apply Fintype.card_of_subtype (Finset.univ.filter
      (fun z : PureLists D x S => pureListProduct D x S z = v))
    intro z
    simp
  have hcount :
      (Finset.univ.filter
        (fun z : PureLists D x S => pureListProduct D x S z = v)).card ≤
        (D.r₀.factorial) ^ (D.last x + 1) := by
    calc
      (Finset.univ.filter
        (fun z : PureLists D x S => pureListProduct D x S z = v)).card =
          Fintype.card Fiber := hcard.symm
      _ ≤ (D.r₀.factorial) ^ (D.last x + 1) :=
        pure_list_fiber_card_le_factorial_pow D x S v hxdisj
  exact_mod_cast hcount


abbrev SelectedProcessedIndex (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool) :=
  {i : Erdos821.S56Core.ProcessedIndex D x jstar // delta i = take}

def selectedProcessedSlot (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool)
    (i : SelectedProcessedIndex D x jstar delta take) : D.Slot x :=
  Erdos821.S56Core.processedSlot D x jstar i.val

def selectedProcessedSlots (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool) :
    Finset (D.Slot x) :=
  Finset.univ.image (selectedProcessedSlot D x jstar delta take)

def selectedProcessedSlotEquiv (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool) :
    SelectedProcessedIndex D x jstar delta take ≃
      {s : D.Slot x // s ∈ selectedProcessedSlots D x jstar delta take} := by
  classical
  refine Equiv.ofBijective
    (fun i => ⟨selectedProcessedSlot D x jstar delta take i,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) ?_
  constructor
  · intro i j hij
    apply Subtype.ext
    exact Erdos821.S56Core.processedSlot_injective D x jstar
      (congrArg Subtype.val hij)
  · intro s
    rcases Finset.mem_image.mp s.property with ⟨i, -, hi⟩
    refine ⟨i, ?_⟩
    exact Subtype.ext hi

theorem selectedProcessedSlotEquiv_val (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool)
    (i : SelectedProcessedIndex D x jstar delta take) :
    (selectedProcessedSlotEquiv D x jstar delta take i).val =
      selectedProcessedSlot D x jstar delta take i := rfl

def selectedProcessedListsEquiv (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool)
    (e : SelectedProcessedIndex D x jstar delta take ≃
      {s : D.Slot x // s ∈ selectedProcessedSlots D x jstar delta take})
    (happly : ∀ i, (e i).val = selectedProcessedSlot D x jstar delta take i) :
    (∀ i : SelectedProcessedIndex D x jstar delta take,
      Erdos821.S56Core.ProcessedValue D x jstar i.val) ≃
      Erdos821.S56Core.PureLists D x
        (selectedProcessedSlots D x jstar delta take) := by
  classical
  refine
    { toFun := fun z s =>
        ⟨(z (e.symm s)).val, ?_⟩
      invFun := fun z i =>
        ⟨(z (e i)).val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hslot : selectedProcessedSlot D x jstar delta take (e.symm s) = s.val := by
      calc
        _ = (e (e.symm s)).val := (happly _).symm
        _ = s.val := congrArg Subtype.val (e.apply_symm_apply s)
    change (z (e.symm s)).val ∈ D.band x (s.val.1.val)
    have hmem := (z (e.symm s)).property
    change (z (e.symm s)).val ∈
      D.band x (selectedProcessedSlot D x jstar delta take (e.symm s)).1.val at hmem
    simpa only [hslot] using hmem
  · have hslot : (e i).val = selectedProcessedSlot D x jstar delta take i := happly i
    change (z (e i)).val ∈ D.band x (selectedProcessedSlot D x jstar delta take i).1.val
    have hmem := (z (e i)).property
    change (z (e i)).val ∈ D.band x ((e i).val.1.val) at hmem
    simpa only [hslot] using hmem
  · intro z
    funext i
    apply Subtype.ext
    exact congrArg (fun j => (z j).val) (e.symm_apply_apply i)
  · intro z
    funext s
    apply Subtype.ext
    exact congrArg (fun s => (z s).val) (e.apply_symm_apply s)

theorem processedCoefficient_eq_pureCoefficient (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ) (v : ℕ) :
    Erdos821.S56Core.processedCoefficient D x jstar delta take nu v =
      Erdos821.S56Core.pureCoefficient D x
        (selectedProcessedSlots D x jstar delta take)
        (fun s => nu ((selectedProcessedSlotEquiv D x jstar delta take).symm s).val) v := by
  classical
  let I := SelectedProcessedIndex D x jstar delta take
  let S := selectedProcessedSlots D x jstar delta take
  let e := selectedProcessedSlotEquiv D x jstar delta take
  let E := selectedProcessedListsEquiv D x jstar delta take e
    (selectedProcessedSlotEquiv_val D x jstar delta take)
  let xi : {s : D.Slot x // s ∈ S} → ℝ := fun s => nu (e.symm s).val
  have hvalue (z : ∀ i : I, Erdos821.S56Core.ProcessedValue D x jstar i.val) :
      (∏ i, (z i).val) = ∏ s ∈ S.attach, (E z s).val := by
    have hpoint (i : I) : (E z (e i)).val = (z i).val := by
      change (z (e.symm (e i))).val = (z i).val
      exact congrArg (fun j => (z j).val) (e.symm_apply_apply i)
    calc
      (∏ i, (z i).val) = ∏ i, (E z (e i)).val := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (hpoint i).symm
      _ = ∏ s : {s : D.Slot x // s ∈ S}, (E z s).val := by
        exact Equiv.prod_comp e (fun s : {s : D.Slot x // s ∈ S} => (E z s).val)
      _ = ∏ s ∈ S.attach, (E z s).val := by
        exact Finset.prod_coe_sort_eq_attach (s := S) (f := fun s => (E z s).val)
  have hweight (z : ∀ i : I, Erdos821.S56Core.ProcessedValue D x jstar i.val) :
      (∏ i, Erdos821.Blueprint.Analytic.mellin (z i).val (nu i.val)) =
        ∏ s ∈ S.attach,
          Erdos821.Blueprint.Analytic.mellin (E z s).val (xi s) := by
    have hpoint (i : I) : (E z (e i)).val = (z i).val := by
      change (z (e.symm (e i))).val = (z i).val
      exact congrArg (fun j => (z j).val) (e.symm_apply_apply i)
    have hxi (i : I) : xi (e i) = nu i.val := by
      change nu (e.symm (e i)).val = nu i.val
      exact congrArg (fun j => nu j.val) (e.symm_apply_apply i)
    calc
      (∏ i, Erdos821.Blueprint.Analytic.mellin (z i).val (nu i.val)) =
          ∏ i, Erdos821.Blueprint.Analytic.mellin (E z (e i)).val (xi (e i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [← hpoint i, ← hxi i]
      _ = ∏ s : {s : D.Slot x // s ∈ S},
          Erdos821.Blueprint.Analytic.mellin (E z s).val (xi s) := by
        exact Equiv.prod_comp e (fun s : {s : D.Slot x // s ∈ S} =>
          Erdos821.Blueprint.Analytic.mellin (E z s).val (xi s))
      _ = ∏ s ∈ S.attach,
          Erdos821.Blueprint.Analytic.mellin (E z s).val (xi s) := by
        exact Finset.prod_coe_sort_eq_attach (s := S)
          (f := fun s => Erdos821.Blueprint.Analytic.mellin (E z s).val (xi s))
  unfold Erdos821.S56Core.processedCoefficient Erdos821.S56Core.pureCoefficient
  unfold Erdos821.S56Core.productCoefficient
  rw [← E.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro z hz
  have hv := hvalue (E.symm z)
  have hw := hweight (E.symm z)
  have hv' :
      (∏ i : I, ((E.symm z) i).val) = ∏ s ∈ S.attach, (z s).val := by
    simpa using hv
  have hw' :
      (∏ i : I, Erdos821.Blueprint.Analytic.mellin ((E.symm z) i).val (nu i.val)) =
        ∏ s ∈ S.attach,
          Erdos821.Blueprint.Analytic.mellin (z s).val (xi s) := by
    simpa using hw
  change
    (if (∏ i : I, ((E.symm z) i).val) = v then
      ∏ i : I, Erdos821.Blueprint.Analytic.mellin ((E.symm z) i).val (nu i.val) else 0) =
    (if (∏ s ∈ S.attach, (z s).val) = v then
      ∏ s ∈ S.attach,
        Erdos821.Blueprint.Analytic.mellin (z s).val (xi s) else 0)
  rw [hv', hw']

theorem processedCoefficientBoundTask_proof :
    Erdos821.S56Core.ProcessedCoefficientBoundTask := by
  intro hCount D hD
  have hSource : Erdos821.S56Core.PureSlotMultiplicityTask := by
    intro D' hD'
    simpa [Erdos821.S56Core.PureLists, Erdos821.S56Core.pureListProduct,
      PureLists, pureListProduct] using hCount D' hD'
  obtain ⟨C, hC, hx⟩ := Erdos821.S56Core.pure_coefficients_polylog hSource D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hx] with x hx
  intro jstar delta take nu v
  let S := selectedProcessedSlots D x jstar delta take
  let xi : {s : D.Slot x // s ∈ S} → ℝ := fun s =>
    nu ((selectedProcessedSlotEquiv D x jstar delta take).symm s).val
  rw [processedCoefficient_eq_pureCoefficient]
  exact hx S xi v


end Erdos821.P6Slot
