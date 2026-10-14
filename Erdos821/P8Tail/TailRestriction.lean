import Erdos821.P8.TailRestrictionTask

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Tail

/-- Auxiliary identity with the filtered set unfolded (definitionally the task). -/
theorem tailRestrictionAux (I P : Finset ℕ) (M k : ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hI : ∀ n ∈ I, n ≤ M) (F : ℕ → ℝ) :
    (∑ f : Fin k → {p : ℕ // p ∈ P},
      if (∃ q ∈ P, q * (∏ i, (f i).val) ∈ I)
      then F (∏ i, (f i).val) else 0) =
    (∑ f : Fin k → {p : ℕ // p ∈ P.filter (fun p => p ≤ M)},
      if (∃ q ∈ P.filter (fun p => p ≤ M), q * (∏ i, (f i).val) ∈ I)
      then F (∏ i, (f i).val) else 0) := by
  classical
  -- Name the filtered set.
  set Q : Finset ℕ := P.filter (fun p => p ≤ M) with hQdef
  have hQP : ∀ x : ℕ, x ∈ Q → x ∈ P := fun x hx => (Finset.mem_filter.mp hx).1
  -- Inclusion of subtypes and its lift to tuples.
  let ι : {p : ℕ // p ∈ Q} → {p : ℕ // p ∈ P} :=
    fun x => ⟨x.val, hQP _ x.property⟩
  have hι_inj : Function.Injective ι := by
    intro a b hab
    have h1 : (ι a).val = (ι b).val := congrArg Subtype.val hab
    have hval : a.val = b.val := h1
    exact Subtype.ext hval
  let E : (Fin k → {p : ℕ // p ∈ Q}) → (Fin k → {p : ℕ // p ∈ P}) :=
    fun g i => ι (g i)
  have hE_val : ∀ (g : Fin k → {p : ℕ // p ∈ Q}) (i : Fin k),
      ((E g) i).val = (g i).val := fun g i => rfl
  have hE_inj : Function.Injective E := by
    intro g₁ g₂ h
    funext i
    have hval : ((E g₁) i).val = ((E g₂) i).val :=
      congrArg Subtype.val (congrFun h i)
    have hval' : (g₁ i).val = (g₂ i).val := hval
    exact Subtype.ext hval'
  -- Every label is at least 1, so every product is at least 1.
  have hvalP : ∀ (f : Fin k → {p : ℕ // p ∈ P}) (i : Fin k), 1 ≤ (f i).val :=
    fun f i => hP _ (f i).property
  have hvalQ : ∀ (g : Fin k → {p : ℕ // p ∈ Q}) (i : Fin k), 1 ≤ (g i).val :=
    fun g i => hP _ (hQP _ (g i).property)
  have hprodP : ∀ f : Fin k → {p : ℕ // p ∈ P}, 1 ≤ ∏ i, (f i).val := by
    intro f
    have h := Finset.one_le_prod (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => (f i).val) (fun i _ => hvalP f i)
    simpa using h
  have hprodQ : ∀ g : Fin k → {p : ℕ // p ∈ Q}, 1 ≤ ∏ i, (g i).val := by
    intro g
    have h := Finset.one_le_prod (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => (g i).val) (fun i _ => hvalQ g i)
    simpa using h
  -- Every factor is bounded by the product.
  have hfactorP : ∀ (f : Fin k → {p : ℕ // p ∈ P}) (j : Fin k),
      (f j).val ≤ ∏ i, (f i).val := by
    intro f j
    have h := Finset.single_le_prod (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => (f i).val) (fun i _ => hvalP f i) (Finset.mem_univ j)
    simpa using h
  -- Products are preserved by the embedding.
  have hprod_eq : ∀ g : Fin k → {p : ℕ // p ∈ Q},
      ∏ i, ((E g) i).val = ∏ i, (g i).val := by
    intro g
    apply Finset.prod_congr rfl
    intro i _
    rfl
  -- An active witness forces both the witness and every factor below M.
  have hbound_of_active : ∀ (f : Fin k → {p : ℕ // p ∈ P}) (q : ℕ),
      q ∈ P → q * ∏ i, (f i).val ∈ I → q ≤ M ∧ ∀ i, (f i).val ≤ M := by
    intro f q hqP hmem
    have hq1 : 1 ≤ q := hP q hqP
    have hprod1 : 1 ≤ ∏ i, (f i).val := hprodP f
    have hleM : q * ∏ i, (f i).val ≤ M := hI _ hmem
    have hqM : q ≤ M := by
      have h1 : q * 1 ≤ q * ∏ i, (f i).val :=
        mul_le_mul_of_nonneg_left hprod1 (Nat.zero_le q)
      simpa using le_trans h1 hleM
    have hprodM : ∏ i, (f i).val ≤ M := by
      have h1 : 1 * ∏ i, (f i).val ≤ q * ∏ i, (f i).val :=
        mul_le_mul_of_nonneg_right hq1 (Nat.zero_le _)
      simpa using le_trans h1 hleM
    exact ⟨hqM, fun i => le_trans (hfactorP f i) hprodM⟩
  -- The gating condition is the same on either side for embedded tuples.
  have hActive_iff : ∀ g : Fin k → {p : ℕ // p ∈ Q},
      (∃ q ∈ P, q * ∏ i, ((E g) i).val ∈ I) ↔
      (∃ q ∈ Q, q * ∏ i, (g i).val ∈ I) := by
    intro g
    rw [hprod_eq g]
    constructor
    · rintro ⟨q, hqP, hmem⟩
      have hq1 : 1 ≤ q := hP q hqP
      have hprod1 : 1 ≤ ∏ i, (g i).val := hprodQ g
      have hleM : q * ∏ i, (g i).val ≤ M := hI _ hmem
      have hqM : q ≤ M := by
        have h1 : q * 1 ≤ q * ∏ i, (g i).val :=
          mul_le_mul_of_nonneg_left hprod1 (Nat.zero_le q)
        simpa using le_trans h1 hleM
      exact ⟨q, Finset.mem_filter.mpr ⟨hqP, hqM⟩, hmem⟩
    · rintro ⟨q, hqQ, hmem⟩
      exact ⟨q, hQP _ hqQ, hmem⟩
  -- Terms outside the embedded image vanish.
  have hterm_zero_outside :
      ∀ f ∈ (Finset.univ : Finset (Fin k → {p : ℕ // p ∈ P})) \
        Finset.univ.image E,
      (if (∃ q ∈ P, q * (∏ i, (f i).val) ∈ I)
        then F (∏ i, (f i).val) else 0) = 0 := by
    intro f hf
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hf
    -- hf : f ∉ image E
    rw [if_neg]
    rintro ⟨q, hqP, hmem⟩
    apply hf
    obtain ⟨hqM, hfacM⟩ := hbound_of_active f q hqP hmem
    have hmemQ : ∀ i : Fin k, (f i).val ∈ Q := by
      intro i
      rw [hQdef]
      exact Finset.mem_filter.mpr ⟨(f i).property, hfacM i⟩
    refine Finset.mem_image.mpr ⟨fun i => ⟨(f i).val, hmemQ i⟩, Finset.mem_univ _, ?_⟩
    funext i
    apply Subtype.ext
    rfl
  -- Rewrite the left sum as a sum over the image, then reindex.
  have hLHS_eq_image :
      (∑ f : Fin k → {p : ℕ // p ∈ P},
        (if (∃ q ∈ P, q * (∏ i, (f i).val) ∈ I)
          then F (∏ i, (f i).val) else 0)) =
      ∑ f ∈ Finset.univ.image E,
        (if (∃ q ∈ P, q * (∏ i, (f i).val) ∈ I)
          then F (∏ i, (f i).val) else 0) := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro f _ hfN
    have hfmem : f ∈ (Finset.univ : Finset (Fin k → {p : ℕ // p ∈ P})) \
        Finset.univ.image E :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ f, hfN⟩
    exact hterm_zero_outside f hfmem
  have hInjOn : Set.InjOn E ↑(Finset.univ : Finset (Fin k → {p : ℕ // p ∈ Q})) := by
    rw [Finset.coe_univ]
    exact Set.injOn_univ.mpr hE_inj
  have himage_eq :
      (∑ f ∈ Finset.univ.image E,
        (if (∃ q ∈ P, q * (∏ i, (f i).val) ∈ I)
          then F (∏ i, (f i).val) else 0)) =
      (∑ g : Fin k → {p : ℕ // p ∈ Q},
        (if (∃ q ∈ P, q * (∏ i, ((E g) i).val) ∈ I)
          then F (∏ i, ((E g) i).val) else 0)) := by
    rw [Finset.sum_image hInjOn]
  have hpoint : ∀ g : Fin k → {p : ℕ // p ∈ Q},
      (if (∃ q ∈ P, q * (∏ i, ((E g) i).val) ∈ I)
        then F (∏ i, ((E g) i).val) else 0) =
      (if (∃ q ∈ Q, q * (∏ i, (g i).val) ∈ I)
        then F (∏ i, (g i).val) else 0) := by
    intro g
    rw [hprod_eq g]
    by_cases h : (∃ q ∈ Q, q * ∏ i, (g i).val ∈ I)
    · have hP' : (∃ q ∈ P, q * ∏ i, (g i).val ∈ I) := by
        obtain ⟨q, hqQ, hmem⟩ := h
        exact ⟨q, hQP _ hqQ, hmem⟩
      rw [if_pos hP', if_pos h]
    · have hP' : ¬ (∃ q ∈ P, q * ∏ i, (g i).val ∈ I) := by
        rintro ⟨q, hqP, hmem⟩
        apply h
        have hq1 : 1 ≤ q := hP q hqP
        have hprod1 : 1 ≤ ∏ i, (g i).val := hprodQ g
        have hleM : q * ∏ i, (g i).val ≤ M := hI _ hmem
        have hqM : q ≤ M := by
          have h1 : q * 1 ≤ q * ∏ i, (g i).val :=
            mul_le_mul_of_nonneg_left hprod1 (Nat.zero_le q)
          simpa using le_trans h1 hleM
        exact ⟨q, Finset.mem_filter.mpr ⟨hqP, hqM⟩, hmem⟩
      rw [if_neg hP', if_neg h]
  calc
    (∑ f : Fin k → {p : ℕ // p ∈ P},
      if (∃ q ∈ P, q * (∏ i, (f i).val) ∈ I)
      then F (∏ i, (f i).val) else 0)
        = ∑ f ∈ Finset.univ.image E,
          (if (∃ q ∈ P, q * (∏ i, (f i).val) ∈ I)
            then F (∏ i, (f i).val) else 0) := hLHS_eq_image
    _ = (∑ g : Fin k → {p : ℕ // p ∈ Q},
          (if (∃ q ∈ P, q * (∏ i, ((E g) i).val) ∈ I)
            then F (∏ i, ((E g) i).val) else 0)) := himage_eq
    _ = (∑ g : Fin k → {p : ℕ // p ∈ Q},
          (if (∃ q ∈ Q, q * (∏ i, (g i).val) ∈ I)
            then F (∏ i, (g i).val) else 0)) :=
        Finset.sum_congr rfl (fun g _ => hpoint g)

end Erdos821.P8Tail

namespace Erdos821.P8Core

/-- Proof of the tail restriction identity: active labels are all `≤ M`. -/
theorem TailRestrictionTask_proof : TailRestrictionTask := by
  intro I P M k hP hI F
  exact Erdos821.P8Tail.tailRestrictionAux I P M k hP hI F

-- The proof has exactly the stated type.
example : TailRestrictionTask := TailRestrictionTask_proof

end Erdos821.P8Core
