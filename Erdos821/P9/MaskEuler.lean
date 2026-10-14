import Erdos821.P9.PairSieve

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section

def maskTerm (P : Finset ℕ) (q : ℝ) (A : Finset ℕ) : ℝ :=
  q ^ A.card * (1 - q) ^ (P.card - A.card) *
    ∏ p ∈ A, (1 - 1 / (p : ℝ))⁻¹

def maskSum (P : Finset ℕ) (q : ℝ) : ℝ :=
  ∑ A ∈ P.powerset, maskTerm P q A

theorem mask_expectation (P : Finset ℕ) (q : ℝ) :
    maskSum P q = ∏ p ∈ P, (1 - q + q / (1 - 1 / (p : ℝ))) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [maskSum, maskTerm]
  | @insert p P hp ih =>
      have hdisj : Disjoint P.powerset (P.powerset.image (insert p)) := by
        refine Finset.disjoint_left.mpr ?_
        intro A hA hImage
        obtain ⟨B, hB, hEq⟩ := Finset.mem_image.mp hImage
        have hnot : p ∉ A := Finset.notMem_of_mem_powerset_of_notMem hA hp
        have hmem : p ∈ A := by rw [← hEq]; simp
        exact hnot hmem
      have hsumImage (f : Finset ℕ → ℝ) :
          (∑ A ∈ P.powerset.image (insert p), f A) =
            ∑ A ∈ P.powerset, f (insert p A) := by
        rw [Finset.sum_image (by
          intro A hA B hB hEq
          have hnotA : p ∉ A := Finset.notMem_of_mem_powerset_of_notMem hA hp
          have hnotB : p ∉ B := Finset.notMem_of_mem_powerset_of_notMem hB hp
          apply Finset.ext
          intro n
          by_cases hnp : n = p
          · subst n
            simp [hnotA, hnotB]
          · have hx := congrArg (fun s : Finset ℕ => n ∈ s) hEq
            simpa [Finset.mem_insert, hnp] using hx)]
      have hfirst :
          (∑ A ∈ P.powerset, maskTerm (insert p P) q A) =
            (1 - q) * maskSum P q := by
        calc
          (∑ A ∈ P.powerset, maskTerm (insert p P) q A) =
              ∑ A ∈ P.powerset, (1 - q) * maskTerm P q A := by
            apply Finset.sum_congr rfl
            intro A hA
            have hAcard : A.card ≤ P.card := Finset.card_le_card (Finset.mem_powerset.mp hA)
            have hexp : P.card + 1 - A.card = (P.card - A.card) + 1 := by omega
            have hnot : p ∉ A := Finset.notMem_of_mem_powerset_of_notMem hA hp
            simp [maskTerm, Finset.card_insert_of_notMem hp, hexp, hnot, pow_succ]
            ring
          _ = (1 - q) * maskSum P q := by simp [maskSum, Finset.mul_sum]
      have hsecond :
          (∑ A ∈ P.powerset.image (insert p), maskTerm (insert p P) q A) =
            (q * (1 - 1 / (p : ℝ))⁻¹) * maskSum P q := by
        rw [hsumImage]
        calc
          (∑ A ∈ P.powerset, maskTerm (insert p P) q (insert p A)) =
              ∑ A ∈ P.powerset,
                (q * (1 - 1 / (p : ℝ))⁻¹) * maskTerm P q A := by
            apply Finset.sum_congr rfl
            intro A hA
            have hAcard : A.card ≤ P.card := Finset.card_le_card (Finset.mem_powerset.mp hA)
            have hAcard' : (insert p A).card = A.card + 1 := Finset.card_insert_of_notMem
              (Finset.notMem_of_mem_powerset_of_notMem hA hp)
            have hPcard : (insert p P).card = P.card + 1 := Finset.card_insert_of_notMem hp
            have hexp : P.card + 1 - (A.card + 1) = P.card - A.card := by omega
            have hnot : p ∉ A := Finset.notMem_of_mem_powerset_of_notMem hA hp
            simp [maskTerm, hPcard, hAcard', hexp, Finset.prod_insert, hnot, pow_succ]
            ring
          _ = (q * (1 - 1 / (p : ℝ))⁻¹) * maskSum P q := by
            simp [maskSum, Finset.mul_sum]
      rw [maskSum, Finset.powerset_insert, Finset.sum_union hdisj,
        hfirst, hsecond, ih, Finset.prod_insert hp]
      ring


abbrev PermissionIndex (P : Finset ℕ) := {p // p ∈ P}

def permissionEventTerm (P : Finset ℕ) (q : ℝ) (n : ℕ)
    (allow : PermissionIndex P → Bool) : ℝ :=
  ∏ p : PermissionIndex P,
    (if allow p then q else 1 - q) *
      (if allow p then 1 else if p.val ∣ n then 0 else 1)

def permissionEventSum (P : Finset ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  ∑ allow : PermissionIndex P → Bool, permissionEventTerm P q n allow

theorem permission_event_sum_eq (P : Finset ℕ) (q : ℝ) (n : ℕ) :
    permissionEventSum P q n =
      q ^ (P.filter fun p => p ∣ n).card := by
  classical
  calc
    permissionEventSum P q n =
        ∏ p : PermissionIndex P,
          ∑ b : Bool,
            (if b then q else 1 - q) *
              (if b then 1 else if p.val ∣ n then 0 else 1) := by
      unfold permissionEventSum permissionEventTerm
      exact (Fintype.prod_sum
        (κ := fun _ : PermissionIndex P => Bool)
        (f := fun p b =>
          (if b then q else 1 - q) *
            (if b then 1 else if p.val ∣ n then 0 else 1))).symm
    _ = ∏ p : PermissionIndex P, (if p.val ∣ n then q else 1) := by
      apply Fintype.prod_congr
      intro p
      by_cases hp : p.val ∣ n <;> simp [hp] <;> ring
    _ = ∏ p ∈ P, (if p ∣ n then q else 1) := by
      exact Finset.prod_coe_sort P (fun p => if p ∣ n then q else 1)
    _ = q ^ (P.filter fun p => p ∣ n).card := by
      rw [← Finset.prod_filter (s := P) (p := fun p : ℕ => p ∣ n)
        (f := fun _ => q)]
      simp


def permissionGroupEuler (P : Finset ℕ) (q : ℝ) : ℝ :=
  ∏ p ∈ P, (1 + q / ((p : ℝ) - 1))

def permissionMarkedEuler (P : Finset ℕ) (q : ℝ) : ℝ :=
  permissionGroupEuler P q *
    (∑ p ∈ P, 1 / ((p : ℝ) - 1 + q)) / (∑ p ∈ P, 1 / (p : ℝ))

/-- The marked harmonic factor dominates the permission Euler product. -/
theorem permission_euler_le_marked (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) (hne : P.Nonempty) :
    permissionGroupEuler P q ≤ permissionMarkedEuler P q := by
  classical
  have hp1 (p : ℕ) (hp : p ∈ P) : (1 : ℝ) < p := by
    exact_mod_cast (hP p hp).one_lt
  have hV : 0 < ∑ p ∈ P, 1 / (p : ℝ) := by
    apply Finset.sum_pos
    · intro p hp
      exact one_div_pos.mpr (lt_trans zero_lt_one (hp1 p hp))
    · exact hne
  have hsum : (∑ p ∈ P, 1 / (p : ℝ)) ≤
      ∑ p ∈ P, 1 / ((p : ℝ) - 1 + q) := by
    apply Finset.sum_le_sum
    intro p hp
    have hden : 0 < (p : ℝ) - 1 + q := by linarith [hp1 p hp]
    exact one_div_le_one_div_of_le hden (by linarith [hp1 p hp, hq'])
  have hF : 0 ≤ permissionGroupEuler P q := by
    apply Finset.prod_nonneg
    intro p hp
    have hden : 0 < (p : ℝ) - 1 := by linarith [hp1 p hp]
    exact add_nonneg zero_le_one (div_nonneg hq hden.le)
  unfold permissionMarkedEuler
  exact (le_div_iff₀ hV).mpr (mul_le_mul_of_nonneg_left hsum hF)


end

end Erdos821.P9Core
