import Erdos821.S56.Definitions

namespace Erdos821.S56
open scoped BigOperators

private theorem residual_snoc (n : ℕ) (target : ℝ) (v : Fin (n + 1) → ℝ)
    (δ : Fin n → Bool) (b : Bool) (i : ℕ) (hi : i ≤ n) :
    residual target v (Fin.snoc δ b) i =
      residual target (fun j => v j.castSucc) δ i := by
  classical
  simp only [residual, Finset.sum_filter, Fin.sum_univ_castSucc, Fin.val_last,
    if_neg (Nat.not_lt.mpr hi), add_zero, Fin.val_castSucc, Fin.snoc_castSucc]

private theorem branchMass_snoc (n : ℕ) (target : ℝ) (v s : Fin (n + 1) → ℝ)
    (γ : ℝ → ℝ) (δ : Fin n → Bool) (b : Bool) :
    branchMass target v s γ (Fin.snoc δ b) =
      branchMass target (fun i => v i.castSucc) (fun i => s i.castSucc) γ δ *
        (if b then γ ((residual target (fun i => v i.castSucc) δ n - v (Fin.last n)) / s (Fin.last n))
         else 1 - γ ((residual target (fun i => v i.castSucc) δ n - v (Fin.last n)) / s (Fin.last n))) := by
  classical
  unfold branchMass
  rw [Fin.prod_univ_castSucc]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    simp only [Fin.snoc_castSucc, Fin.val_castSucc,
      residual_snoc n target v δ b i.val i.isLt.le]
  · simp only [Fin.snoc_last, Fin.val_last, residual_snoc n target v δ b n le_rfl]

/-- The sequential binary allocation preserves total mass exactly, before Fourier separation. -/
theorem branch_partition_proved (n : ℕ) (target : ℝ) (v s : Fin n → ℝ) (γ : ℝ → ℝ) :
    (∑ δ : Fin n → Bool, branchMass target v s γ δ) = 1 := by
  classical
  induction n with
  | zero => simp [branchMass]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
      (fun δ => branchMass target v s γ δ)]
    simp only [Fintype.sum_prod_type]
    change (∑ b : Bool, ∑ δ : Fin n → Bool, branchMass target v s γ (Fin.snoc δ b)) = 1
    simp_rw [branchMass_snoc]
    rw [Finset.sum_comm]
    have hbool : ∀ δ : Fin n → Bool,
        (∑ b : Bool,
          branchMass target (fun i => v i.castSucc) (fun i => s i.castSucc) γ δ *
            (if b then γ ((residual target (fun i => v i.castSucc) δ n - v (Fin.last n)) / s (Fin.last n))
             else 1 - γ ((residual target (fun i => v i.castSucc) δ n - v (Fin.last n)) / s (Fin.last n)))) =
          branchMass target (fun i => v i.castSucc) (fun i => s i.castSucc) γ δ := by
      intro δ
      simp
      ring
    simp_rw [hbool]
    exact ih (fun i => v i.castSucc) (fun i => s i.castSucc)


end Erdos821.S56
