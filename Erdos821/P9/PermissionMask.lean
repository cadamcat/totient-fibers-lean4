import Erdos821.P9.MaskEuler

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

def permissionMaskProbability (P : Finset ℕ) (q : ℝ)
    (allow : PermissionIndex P → Bool) : ℝ :=
  ∏ p : PermissionIndex P, if allow p then q else 1 - q

def permissionMaskGood (P : Finset ℕ) (n : ℕ)
    (allow : PermissionIndex P → Bool) : Prop :=
  ∀ p : PermissionIndex P, allow p = true ∨ ¬ p.val ∣ n

theorem permissionEventTerm_eq_probability_indicator
    (P : Finset ℕ) (q : ℝ) (n : ℕ) (allow : PermissionIndex P → Bool) :
    permissionEventTerm P q n allow =
      permissionMaskProbability P q allow *
        (if permissionMaskGood P n allow then 1 else 0) := by
  classical
  have hgoodProduct :
      (∏ p ∈ P.attach,
        if allow p then (1 : ℝ) else if p.val ∣ n then 0 else 1) =
        (if permissionMaskGood P n allow then 1 else 0) := by
    by_cases hgood : permissionMaskGood P n allow
    · have hprod :
          (∏ p ∈ P.attach,
            if allow p then (1 : ℝ) else if p.val ∣ n then 0 else 1) = 1 := by
        apply Finset.prod_eq_one
        intro p hp
        by_cases ha : allow p = true
        · simp [ha]
        · have hnot := (hgood p).resolve_left ha
          have hfalse : allow p = false := by
            cases hv : allow p
            · rfl
            · exact (ha hv).elim
          simp [hfalse, hnot]
      simp [hgood, hprod]
    · have hbad : ∃ p : PermissionIndex P, allow p = false ∧ p.val ∣ n := by
        unfold permissionMaskGood at hgood
        push_neg at hgood
        rcases hgood with ⟨⟨p, hpP⟩, hnot, hdiv⟩
        let p' : PermissionIndex P := ⟨p, hpP⟩
        have hfalse : allow p' = false := by
          cases hv : allow p'
          · rfl
          · exact (hnot hv).elim
        exact ⟨p', hfalse, hdiv⟩
      obtain ⟨p, hpFalse, hpDiv⟩ := hbad
      have hfactor : (if allow p then (1 : ℝ) else if p.val ∣ n then 0 else 1) = 0 := by
        simp [hpFalse, hpDiv]
      have hpMem : p ∈ P.attach := Finset.mem_attach _ _
      have hprod :
          (∏ p ∈ P.attach,
            if allow p then (1 : ℝ) else if p.val ∣ n then 0 else 1) = 0 :=
        Finset.prod_eq_zero hpMem hfactor
      simp [hgood, hprod]
  unfold permissionEventTerm permissionMaskProbability
  have hprob :
      (∏ p ∈ P.attach, if allow p then q else 1 - q) =
        ∏ p : PermissionIndex P, if allow p then q else 1 - q := by
    rw [← Finset.univ_eq_attach]
  calc
    (∏ p ∈ P.attach,
      (if allow p then q else 1 - q) *
        (if allow p then 1 else if p.val ∣ n then 0 else 1)) =
      (∏ p ∈ P.attach, if allow p then q else 1 - q) *
        (∏ p ∈ P.attach,
          if allow p then (1 : ℝ) else if p.val ∣ n then 0 else 1) :=
        Finset.prod_mul_distrib
    _ = (∏ p : PermissionIndex P, if allow p then q else 1 - q) *
          (if permissionMaskGood P n allow then 1 else 0) := by
      calc
        _ = (∏ p ∈ P.attach, if allow p then q else 1 - q) *
              (if permissionMaskGood P n allow then 1 else 0) :=
          congrArg (fun y : ℝ =>
            (∏ p ∈ P.attach, if allow p then q else 1 - q) * y) hgoodProduct
        _ = _ := by rw [hprob]

theorem permissionMaskProbability_sum_eq_one (P : Finset ℕ) (q : ℝ) :
    (∑ allow : PermissionIndex P → Bool,
      permissionMaskProbability P q allow) = 1 := by
  classical
  calc
    (∑ allow : PermissionIndex P → Bool,
      permissionMaskProbability P q allow) =
        ∏ p : PermissionIndex P, ∑ b : Bool, (if b then q else 1 - q) := by
      unfold permissionMaskProbability
      exact (Fintype.prod_sum
        (κ := fun _ : PermissionIndex P => Bool)
        (f := fun _ b => if b then q else 1 - q)).symm
    _ = 1 := by simp


end

end Erdos821.P9Core
