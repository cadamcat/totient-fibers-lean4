import Erdos821.P9.PairSieve

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

noncomputable def squarefree_zmod_equiv_prime_factors (d : ℕ) (hd : d ≠ 0) (hsq : Squarefree d) :
    ZMod d ≃+* (∀ p : d.primeFactors, ZMod p.val) := by
  have hfactor : ∀ p : d.primeFactors, d.factorization p.val = 1 := by
    intro p
    have hpDvd : p.val ∣ d := (Nat.mem_primeFactors.mp p.property).2.1
    have hpPrime : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
    have hpos : 0 < d.factorization p.val := hpPrime.factorization_pos_of_dvd hd hpDvd
    have hle : d.factorization p.val ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hd).mp hsq p.val
    omega
  have hpow : ∀ p : d.primeFactors, p.val ^ d.factorization p.val = p.val := by
    intro p
    rw [hfactor p, pow_one]
  exact (ZMod.equivPi d hd).trans (RingEquiv.piCongrRight fun p => RingEquiv.cast (hpow p))

def pairBadCount (p : ℕ) (belowW banned : Bool) : ℕ :=
  (if belowW then 2 * p - 1 else 0) + (if banned then p - 1 else 0)

theorem pairBadCount_le_square (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (belowW banned : Bool) : pairBadCount p belowW banned ≤ p ^ 2 := by
  have hlinear : pairBadCount p belowW banned ≤ 3 * p := by
    cases belowW <;> cases banned <;> simp [pairBadCount] <;> omega
  have hsq : 3 * p ≤ p ^ 2 := by
    calc
      3 * p ≤ p * p := Nat.mul_le_mul_right p hp3
      _ = p ^ 2 := by ring
  exact hlinear.trans hsq

def pairBadLocal (p : ℕ) (belowW banned : Bool) (v : ZMod p × ZMod p) : Prop :=
  (if belowW then v.1 * v.2 = 0 else False) ∨
    (if banned then v.1 * v.2 = 1 else False)

noncomputable def pairBadRoots (p : ℕ) [NeZero p] (belowW banned : Bool) :
    Finset (ZMod p × ZMod p) := by
  classical
  exact Finset.univ.filter (pairBadLocal p belowW banned)

theorem pairBadCount_cast_eq_pairNu (p : ℕ) (hp3 : 3 ≤ p)
    (belowW banned : Bool) :
    (pairBadCount p belowW banned : ℝ) = pairNu p belowW banned := by
  have hp1 : 1 ≤ p := by omega
  have hp2 : 1 ≤ 2 * p := by omega
  cases belowW <;> cases banned <;>
    simp [pairBadCount, pairNu, Nat.cast_sub hp1, Nat.cast_sub hp2]

theorem pair_bad_local_count (p : ℕ) [NeZero p] (hp : p.Prime) (hp3 : 3 ≤ p)
    (belowW banned : Bool) :
    (pairBadRoots p belowW banned).card = pairBadCount p belowW banned := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let zeroRoots : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun v => v.1 * v.2 = 0)
  let oneRoots : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun v => v.1 * v.2 = 1)
  have hzeroCount : zeroRoots.card = 2 * p - 1 := by
    simpa [zeroRoots] using (pair_bad_residue_counts p hp).1
  have honeCount : oneRoots.card = p - 1 := by
    simpa [oneRoots] using (pair_bad_residue_counts p hp).2
  have hdisj : Disjoint zeroRoots oneRoots := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hv'
    have h0 := (Finset.mem_filter.mp hv).2
    have h1 := (Finset.mem_filter.mp hv').2
    exact zero_ne_one (h0.symm.trans h1)
  have hrootOne : pairBadRoots p false true = oneRoots := by
    ext v
    simp [pairBadRoots, pairBadLocal, oneRoots]
  have hrootZero : pairBadRoots p true false = zeroRoots := by
    ext v
    simp [pairBadRoots, pairBadLocal, zeroRoots]
  have hrootBoth : pairBadRoots p true true = zeroRoots ∪ oneRoots := by
    ext v
    simp [pairBadRoots, pairBadLocal, zeroRoots, oneRoots]
  cases belowW <;> cases banned
  · simp [pairBadRoots, pairBadLocal, pairBadCount]
  · rw [hrootOne]
    simp [pairBadCount, honeCount]
  · rw [hrootZero]
    simp [pairBadCount, hzeroCount]
  · have hcard : (pairBadRoots p true true).card = zeroRoots.card + oneRoots.card := by
      rw [hrootBoth, Finset.card_union_of_disjoint hdisj]
    simp [pairBadCount, hcard, hzeroCount, honeCount]

theorem pairBadCountProduct_le_square (d : ℕ) (W : ℝ) (P A : Finset ℕ)
    (hsq : Squarefree d) (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p) :
    (∏ p : d.primeFactors,
      pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A))) ≤ d ^ 2 := by
  classical
  let Q := d.primeFactors
  have hprod :
      (∏ p ∈ Q, pairBadCount p (decide ((p : ℝ) ≤ W))
        (decide (p ∉ P ∨ p ∉ A))) ≤ ∏ p ∈ Q, p ^ 2 := by
    apply Finset.prod_le_prod
    intro p hp
    exact pairBadCount_le_square p (Nat.prime_of_mem_primeFactors hp) (hd3 p hp)
      (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))
  have hsubtype₁ :
      (∏ p : d.primeFactors,
        pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A))) =
      ∏ p ∈ Q, pairBadCount p (decide ((p : ℝ) ≤ W))
        (decide (p ∉ P ∨ p ∉ A)) := by
    simpa [Q] using
      (Finset.prod_coe_sort (d.primeFactors : Finset ℕ)
        (fun p : ℕ => pairBadCount p (decide ((p : ℝ) ≤ W))
          (decide (p ∉ P ∨ p ∉ A))) )
  have hsubtype₂ :
      (∏ p : d.primeFactors, p.val ^ 2) = ∏ p ∈ Q, p ^ 2 :=
    by
      simpa [Q] using
        (Finset.prod_coe_sort (d.primeFactors : Finset ℕ) (fun p : ℕ => p ^ 2))
  have hpow : ∏ p ∈ Q, p ^ 2 = (∏ p ∈ Q, p) ^ 2 := by
    rw [Finset.prod_pow]
  rw [hpow, Nat.prod_primeFactors_of_squarefree hsq] at hprod
  rw [hsubtype₁]
  exact hprod

theorem pair_root_tuple_count (d : ℕ) (W : ℝ) (P A : Finset ℕ)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p)
    [∀ p : d.primeFactors, NeZero p.val] :
    Fintype.card
        {v : (p : d.primeFactors) → ZMod p.val × ZMod p.val //
          ∀ p, pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) (v p)} =
      ∏ p : d.primeFactors,
        pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) := by
  classical
  rw [Fintype.card_congr Equiv.subtypePiEquivPi, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro p hpP
  have hpPrime : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
  have hp3 : 3 ≤ p.val := hd3 p p.property
  letI : NeZero p.val := ⟨hpPrime.ne_zero⟩
  have hcard : Fintype.card {v : ZMod p.val × ZMod p.val //
      pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A)) v} =
      pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A)) := by
    simpa [Fintype.card_subtype, pairBadRoots] using
      pair_bad_local_count p.val hpPrime hp3
        (decide ((p.val : ℝ) ≤ W)) (decide (p.val ∉ P ∨ p.val ∉ A))
  exact hcard

abbrev PairPrimeCoordinates (d : ℕ) :=
  (p : d.primeFactors) → ZMod p.val × ZMod p.val

abbrev PrimeCoordinates (d : ℕ) :=
  (p : d.primeFactors) → ZMod p.val

abbrev PairCRTCoordinates (D d : ℕ) :=
  (ZMod D × ZMod D) × PairPrimeCoordinates d

noncomputable def pairRearrange (A B : Type*) :
    ((A × B) × (A × B)) ≃ (A × A) × (B × B) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv x := by cases x with | mk x y => cases x; cases y; rfl
  right_inv x := by cases x with | mk x y => cases x; cases y; rfl

noncomputable def pairFunctionsEquiv {ι : Type*} (A B : ι → Type*) :
    ((i : ι) → A i) × ((i : ι) → B i) ≃ ((i : ι) → A i × B i) where
  toFun f i := (f.1 i, f.2 i)
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv f := by cases f; rfl
  right_inv f := by funext i; exact Prod.eta (f i)

noncomputable def single_crt_equiv (D d : ℕ) (hcop : Nat.Coprime D d)
    (hd : d ≠ 0) (hsq : Squarefree d) :
    ZMod (D * d) ≃+* ZMod D × PrimeCoordinates d := by
  let eD : ZMod (D * d) ≃+* ZMod D × ZMod d := ZMod.chineseRemainder hcop
  let eFactor : ZMod d ≃+* PrimeCoordinates d :=
    squarefree_zmod_equiv_prime_factors d hd hsq
  exact eD.trans (RingEquiv.prodCongr (RingEquiv.refl _) eFactor)

noncomputable def pair_crt_equiv (D d : ℕ) (hcop : Nat.Coprime D d)
    (hd : d ≠ 0) (hsq : Squarefree d) :
    (ZMod (D * d) × ZMod (D * d)) ≃ PairCRTCoordinates D d := by
  let e := single_crt_equiv D d hcop hd hsq
  exact (Equiv.prodCongr e.toEquiv e.toEquiv).trans
    ((pairRearrange (ZMod D) (PrimeCoordinates d)).trans
      (Equiv.prodCongr (Equiv.refl _) (pairFunctionsEquiv _ _)))

def pairBaseReduction (D d : ℕ) : ZMod (D * d) →+* ZMod D :=
  ZMod.castHom (dvd_mul_of_dvd_left (dvd_refl D) d) (ZMod D)

def pairPrimeReduction (D d : ℕ) (p : d.primeFactors) :
    ZMod (D * d) →+* ZMod p.val :=
  ZMod.castHom (dvd_mul_of_dvd_right ((Nat.mem_primeFactors.mp p.property).2.1) D)
    (ZMod p.val)

theorem single_crt_equiv_base_left (D d : ℕ) (hcop : Nat.Coprime D d)
    (hd : d ≠ 0) (hsq : Squarefree d) (x : ZMod (D * d)) :
    (single_crt_equiv D d hcop hd hsq x).1 = pairBaseReduction D d x := by
  let f : ZMod (D * d) →+* ZMod D :=
    (RingHom.fst (ZMod D) (PrimeCoordinates d)).comp
      (single_crt_equiv D d hcop hd hsq).toRingHom
  have hf : f = pairBaseReduction D d := RingHom.ext_zmod f _
  exact congrArg (fun g : ZMod (D * d) →+* ZMod D => g x) hf

theorem single_crt_equiv_prime_apply (D d : ℕ) (hcop : Nat.Coprime D d)
    (hd : d ≠ 0) (hsq : Squarefree d) (p : d.primeFactors)
    (x : ZMod (D * d)) :
    ((single_crt_equiv D d hcop hd hsq x).2 p) = pairPrimeReduction D d p x := by
  let f : ZMod (D * d) →+* ZMod p.val :=
    (Pi.evalRingHom (fun q : d.primeFactors => ZMod q.val) p).comp
      ((RingHom.snd (ZMod D) (PrimeCoordinates d)).comp
        (single_crt_equiv D d hcop hd hsq).toRingHom)
  have hf : f = pairPrimeReduction D d p := RingHom.ext_zmod f _
  simpa [f, single_crt_equiv, RingEquiv.trans_apply, RingHom.comp_apply] using
    congrArg (fun g : ZMod (D * d) →+* ZMod p.val => g x) hf

theorem pair_crt_equiv_base_left (D d : ℕ) (hcop : Nat.Coprime D d)
    (hd : d ≠ 0) (hsq : Squarefree d) (x y : ZMod (D * d)) :
    (pair_crt_equiv D d hcop hd hsq (x, y)).1.1 = pairBaseReduction D d x := by
  change (single_crt_equiv D d hcop hd hsq x).1 = pairBaseReduction D d x
  exact single_crt_equiv_base_left D d hcop hd hsq x

theorem pair_crt_equiv_base_right (D d : ℕ) (hcop : Nat.Coprime D d)
    (hd : d ≠ 0) (hsq : Squarefree d) (x y : ZMod (D * d)) :
    (pair_crt_equiv D d hcop hd hsq (x, y)).1.2 = pairBaseReduction D d y := by
  change (single_crt_equiv D d hcop hd hsq y).1 = pairBaseReduction D d y
  exact single_crt_equiv_base_left D d hcop hd hsq y

theorem pair_crt_equiv_prime_left (D d : ℕ) (hcop : Nat.Coprime D d)
    (hd : d ≠ 0) (hsq : Squarefree d) (p : d.primeFactors)
    (x y : ZMod (D * d)) :
    ((pair_crt_equiv D d hcop hd hsq (x, y)).2 p).1 = pairPrimeReduction D d p x := by
  change ((single_crt_equiv D d hcop hd hsq x).2 p) = pairPrimeReduction D d p x
  exact single_crt_equiv_prime_apply D d hcop hd hsq p x

theorem pair_crt_equiv_prime_right (D d : ℕ) (hcop : Nat.Coprime D d)
    (hd : d ≠ 0) (hsq : Squarefree d) (p : d.primeFactors)
    (x y : ZMod (D * d)) :
    ((pair_crt_equiv D d hcop hd hsq (x, y)).2 p).2 = pairPrimeReduction D d p y := by
  change ((single_crt_equiv D d hcop hd hsq y).2 p) = pairPrimeReduction D d p y
  exact single_crt_equiv_prime_apply D d hcop hd hsq p y

noncomputable def unitPairEquiv (D : ℕ) [NeZero D] :
    {v : ZMod D × ZMod D // v.1 * v.2 = 1} ≃ (ZMod D)ˣ where
  toFun v := Units.mkOfMulEqOne v.val.1 v.val.2 v.property
  invFun u := ⟨(u.val, (u⁻¹ : (ZMod D)ˣ)), u.val_inv⟩
  left_inv v := by
    apply Subtype.ext
    rcases v with ⟨⟨a, b⟩, hab⟩
    simp [Units.mkOfMulEqOne]
  right_inv u := by
    apply Units.ext
    rfl

theorem base_pair_root_count (D : ℕ) [NeZero D] :
    Fintype.card {v : ZMod D × ZMod D // v.1 * v.2 = 1} = D.totient := by
  rw [Fintype.card_congr (unitPairEquiv D), ZMod.card_units_eq_totient]

theorem pair_crt_coordinate_root_count (D d : ℕ) (W : ℝ) (P A : Finset ℕ)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p) [NeZero D]
    [∀ p : d.primeFactors, NeZero p.val] :
    Fintype.card
      {v : PairCRTCoordinates D d //
        v.1.1 * v.1.2 = 1 ∧
          ∀ p, pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) (v.2 p)} =
      D.totient *
        ∏ p : d.primeFactors,
          pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) := by
  classical
  let Base := {v : ZMod D × ZMod D // v.1 * v.2 = 1}
  let Local := {v : PairPrimeCoordinates d //
    ∀ p, pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
      (decide (p.val ∉ P ∨ p.val ∉ A)) (v p)}
  let e : {v : PairCRTCoordinates D d //
        v.1.1 * v.1.2 = 1 ∧
          ∀ p, pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) (v.2 p)} ≃ Base × Local :=
    { toFun := fun v => (⟨v.val.1, v.property.1⟩, ⟨v.val.2, v.property.2⟩)
      invFun := fun v => ⟨(v.1.val, v.2.val), ⟨v.1.property, v.2.property⟩⟩
      left_inv := by intro v; cases v; rfl
      right_inv := by intro v; cases v; rfl }
  have hLocal : Fintype.card Local =
      ∏ p : d.primeFactors,
        pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) := by
    simpa [Local] using pair_root_tuple_count d W P A hd3
  rw [Fintype.card_congr e, Fintype.card_prod, base_pair_root_count, hLocal]

theorem pair_crt_residue_count (D d : ℕ) (W : ℝ) (P A : Finset ℕ)
    (hcop : Nat.Coprime D d) (hD : D ≠ 0) (hd : d ≠ 0) (hsq : Squarefree d)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p) [NeZero D] [NeZero (D * d)]
    [∀ p : d.primeFactors, NeZero p.val] :
    Fintype.card
      {v : ZMod (D * d) × ZMod (D * d) //
        (pair_crt_equiv D d hcop hd hsq v).1.1 *
            (pair_crt_equiv D d hcop hd hsq v).1.2 = 1 ∧
          ∀ p, pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A))
            ((pair_crt_equiv D d hcop hd hsq v).2 p)} =
      Nat.totient D *
        ∏ p : d.primeFactors,
          pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) := by
  classical
  let e := pair_crt_equiv D d hcop hd hsq
  let localGood := fun v : PairCRTCoordinates D d =>
    v.1.1 * v.1.2 = 1 ∧ ∀ p,
      pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A)) (v.2 p)
  have hequiv :
      {v : ZMod (D * d) × ZMod (D * d) // localGood (e v)} ≃
        {v : PairCRTCoordinates D d // localGood v} := by
    refine
      { toFun := fun v => ⟨e v.val, v.property⟩
        invFun := fun v => ⟨e.symm v.val, by simpa using v.property⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro v
      apply Subtype.ext
      simp
    · intro v
      apply Subtype.ext
      simp
  have hcount := pair_crt_coordinate_root_count D d W P A hd3
  have hmain : Fintype.card {v : PairCRTCoordinates D d // localGood v} =
      Nat.totient D * ∏ p : d.primeFactors,
        pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) := by
    simpa [localGood] using hcount
  rw [Fintype.card_congr hequiv]
  simpa [localGood, e] using hmain

theorem pair_crt_divisibility_root_count (D d : ℕ) (W : ℝ) (P A : Finset ℕ)
    (hcop : Nat.Coprime D d) (hD : D ≠ 0) (hd : d ≠ 0) (hsq : Squarefree d)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p) [NeZero D] [NeZero (D * d)]
    [∀ p : d.primeFactors, NeZero p.val] :
    Fintype.card
      {v : ZMod (D * d) × ZMod (D * d) //
        pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧
          ∀ p, pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A))
            (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)} =
      Nat.totient D *
        ∏ p : d.primeFactors,
          pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) := by
  classical
  let directGood := fun v : ZMod (D * d) × ZMod (D * d) =>
    pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧ ∀ p,
      pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A))
        (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)
  let crtGood := fun v : ZMod (D * d) × ZMod (D * d) =>
    (pair_crt_equiv D d hcop hd hsq v).1.1 *
        (pair_crt_equiv D d hcop hd hsq v).1.2 = 1 ∧
      ∀ p, pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A))
        ((pair_crt_equiv D d hcop hd hsq v).2 p)
  have hgood : ∀ v, directGood v ↔ crtGood v := by
    intro v
    rcases v with ⟨x, y⟩
    have hbaseLeft := pair_crt_equiv_base_left D d hcop hd hsq x y
    have hbaseRight := pair_crt_equiv_base_right D d hcop hd hsq x y
    have hprimePair (p : d.primeFactors) :
        ((pair_crt_equiv D d hcop hd hsq (x, y)).2 p) =
          (pairPrimeReduction D d p x, pairPrimeReduction D d p y) := by
      exact Prod.ext
        (pair_crt_equiv_prime_left D d hcop hd hsq p x y)
        (pair_crt_equiv_prime_right D d hcop hd hsq p x y)
    constructor
    · rintro ⟨hbase, hbad⟩
      constructor
      · have hbase' : pairBaseReduction D d x * pairBaseReduction D d y = 1 := by
          simpa using hbase
        rw [hbaseLeft, hbaseRight]
        exact hbase'
      · intro p
        rw [hprimePair p]
        simpa using hbad p
    · rintro ⟨hbase, hbad⟩
      constructor
      · rw [hbaseLeft, hbaseRight] at hbase
        simpa using hbase
      · intro p
        have hp := hbad p
        rw [hprimePair p] at hp
        simpa using hp
  let e : {v : ZMod (D * d) × ZMod (D * d) // directGood v} ≃
      {v : ZMod (D * d) × ZMod (D * d) // crtGood v} :=
    { toFun := fun v => ⟨v.val, (hgood v.val).mp v.property⟩
      invFun := fun v => ⟨v.val, (hgood v.val).mpr v.property⟩
      left_inv := by intro v; apply Subtype.ext; rfl
      right_inv := by intro v; apply Subtype.ext; rfl }
  have hcount := pair_crt_residue_count D d W P A hcop hD hd hsq hd3
  have hcrt : Fintype.card {v : ZMod (D * d) × ZMod (D * d) // crtGood v} =
      Nat.totient D * ∏ p : d.primeFactors,
        pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) := by
    simpa [crtGood] using hcount
  rw [Fintype.card_congr e]
  exact hcrt

theorem pair_crt_divisibility_root_count_le
    (D d : ℕ) (W : ℝ) (P A : Finset ℕ)
    (hcop : Nat.Coprime D d) (hD : D ≠ 0) (hd : d ≠ 0) (hsq : Squarefree d)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p) [NeZero D] [NeZero (D * d)]
    [∀ p : d.primeFactors, NeZero p.val] :
    Fintype.card
      {v : ZMod (D * d) × ZMod (D * d) //
        pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧
          ∀ p, pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A))
            (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)} ≤ D * d ^ 2 := by
  rw [pair_crt_divisibility_root_count D d W P A hcop hD hd hsq hd3]
  have hbad := pairBadCountProduct_le_square d W P A hsq hd3
  exact Nat.mul_le_mul (Nat.totient_le D) hbad




end

end Erdos821.P9Core
