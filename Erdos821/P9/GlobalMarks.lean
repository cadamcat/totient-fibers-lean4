import Erdos821.P9.Assignment

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GlobalMarkOption (G : Erdos821.Blueprint.Analytic.PrimeGroups)
    (g : Fin G.size) := {p : ℕ // p ∈ G.primes g}

abbrev GlobalMarkChoices (G : Erdos821.Blueprint.Analytic.PrimeGroups) :=
  (g : Fin G.size) → GlobalMarkOption G g

def globalMarkProduct (G : Erdos821.Blueprint.Analytic.PrimeGroups)
    (marks : GlobalMarkChoices G) : ℕ :=
  ∏ g, (marks g).val

def globalMarkImage (G : Erdos821.Blueprint.Analytic.PrimeGroups)
    (marks : GlobalMarkChoices G) : Finset ℕ :=
  Finset.univ.image fun g : Fin G.size => (marks g).val

def globalMarksDivide (G : Erdos821.Blueprint.Analytic.PrimeGroups)
    (marks : GlobalMarkChoices G) (n : ℕ) : Prop :=
  ∀ g, (marks g).val ∣ n

def globalMarkDivisors (G : Erdos821.Blueprint.Analytic.PrimeGroups) (n : ℕ) :
    Finset (GlobalMarkChoices G) :=
  Finset.univ.filter fun marks => globalMarksDivide G marks n

noncomputable def markChoicesEquivGlobal (G : Erdos821.Blueprint.Analytic.PrimeGroups)
    (n : ℕ) :
    MarkChoices G n ≃ {marks : GlobalMarkChoices G // globalMarksDivide G marks n} where
  toFun marks :=
    ⟨fun g => ⟨(marks g).val, (Finset.mem_filter.mp (marks g).property).1⟩,
      fun g => (Finset.mem_filter.mp (marks g).property).2⟩
  invFun marks := fun g =>
    ⟨(marks.val g).val,
      Finset.mem_filter.mpr ⟨(marks.val g).property, marks.property g⟩⟩
  left_inv marks := by
    funext g
    apply Subtype.ext
    rfl
  right_inv marks := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    rfl

theorem markProduct_eq_globalMarkProduct
    (G : Erdos821.Blueprint.Analytic.PrimeGroups) (n : ℕ)
    (marks : {m : GlobalMarkChoices G // globalMarksDivide G m n}) :
    markProduct G n (markChoicesEquivGlobal G n |>.invFun marks) =
      globalMarkProduct G marks.val := by
  simp [markProduct, globalMarkProduct, markChoicesEquivGlobal]

theorem markImage_eq_globalMarkImage
    (G : Erdos821.Blueprint.Analytic.PrimeGroups) (n : ℕ)
    (marks : {m : GlobalMarkChoices G // globalMarksDivide G m n}) :
    markImage G n (markChoicesEquivGlobal G n |>.invFun marks) =
      globalMarkImage G marks.val := by
  ext p
  simp [markImage, globalMarkImage, markChoicesEquivGlobal]

theorem sum_markChoices_eq_sum_globalMarkDivisors
    (G : Erdos821.Blueprint.Analytic.PrimeGroups) (n : ℕ)
    (f : MarkChoices G n → ℝ) :
    (∑ marks : MarkChoices G n, f marks) =
      ∑ marks : {m : GlobalMarkChoices G // globalMarksDivide G m n},
        f (markChoicesEquivGlobal G n |>.invFun marks) := by
  exact Fintype.sum_equiv (markChoicesEquivGlobal G n) f
    (fun marks => f ((markChoicesEquivGlobal G n).invFun marks))
    (by intro marks; simp)

theorem sum_globalMarkDivisors_eq_filter
    (G : Erdos821.Blueprint.Analytic.PrimeGroups) (n : ℕ)
    (f : GlobalMarkChoices G → ℝ) :
    (∑ marks : {m : GlobalMarkChoices G // globalMarksDivide G m n}, f marks.val) =
      ∑ marks ∈ globalMarkDivisors G n, f marks := by
  classical
  let s := globalMarkDivisors G n
  let e : {m : GlobalMarkChoices G // globalMarksDivide G m n} ≃
      ↥s := {
    toFun := fun m => (⟨m.val,
      by
        change m.val ∈ Finset.univ.filter
          (fun marks : GlobalMarkChoices G => globalMarksDivide G marks n)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, m.property⟩⟩ : ↥s)
    invFun := fun m => (⟨m.val,
      by
        have hm : m.val ∈ Finset.univ.filter
            (fun marks : GlobalMarkChoices G => globalMarksDivide G marks n) := by
          simpa [s, globalMarkDivisors] using m.property
        exact (Finset.mem_filter.mp hm).2⟩ :
        {m : GlobalMarkChoices G // globalMarksDivide G m n})
    left_inv := by intro m; apply Subtype.ext; rfl
    right_inv := by intro m; apply Subtype.ext; rfl
  }
  calc
    (∑ marks : {m : GlobalMarkChoices G // globalMarksDivide G m n}, f marks.val) =
        ∑ marks : ↥s, f marks.val := by
      exact Fintype.sum_equiv e (fun m => f m.val) (fun m => f m.val)
        (by intro m; simp [e])
    _ = ∑ marks ∈ s.attach, f marks.val := by
      rw [← Finset.univ_eq_attach]
    _ = ∑ marks ∈ globalMarkDivisors G n, f marks := by
      simpa [s] using Finset.sum_attach s f


end

end Erdos821.P9Core
