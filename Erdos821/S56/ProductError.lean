import Mathlib

noncomputable section
open scoped BigOperators

namespace Erdos821.S56Core

theorem product_norm_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hf : ∀ i ∈ s, ‖f i‖ ≤ M) : ‖∏ i ∈ s, f i‖ ≤ M ^ s.card := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _i ∈ s, M := Finset.prod_le_prod₀ (fun i _ => norm_nonneg (f i)) hf
    _ = _ := by simp

/-- A uniform one-variable Fourier error may be summed over all slots
before Cauchy. The fixed M costs only a fixed power per slot. -/
theorem product_error_bound {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (M eps : ℝ) (hM : 1 ≤ M) (heps : 0 ≤ eps)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ M) (hg : ∀ i ∈ s, ‖g i‖ ≤ M)
    (hdiff : ∀ i ∈ s, ‖f i - g i‖ ≤ eps) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ (s.card : ℝ) * eps * M ^ s.card := by
  classical
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  revert hf hg hdiff
  induction s using Finset.induction_on with
  | empty => intro hf hg hdiff; simp
  | @insert i s hi ih =>
    intro hf hg hdiff
    have hf' := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hg' := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hd' := fun j hj => hdiff j (Finset.mem_insert_of_mem hj)
    have hinner := ih hf' hg' hd'
    have hgnorm := product_norm_bound s g M hM0 hg'
    have hi1 := Finset.mem_insert_self i s
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    calc
      _ = ‖f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
          (f i - g i) * ∏ j ∈ s, g j‖ := by congr 1; ring
      _ ≤ ‖f i‖ * ‖(∏ j ∈ s, f j) - ∏ j ∈ s, g j‖ +
          ‖f i - g i‖ * ‖∏ j ∈ s, g j‖ := by
        simpa only [norm_mul] using norm_add_le
          (f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)) ((f i - g i) * ∏ j ∈ s, g j)
      _ ≤ M * ((s.card : ℝ) * eps * M ^ s.card) + eps * M ^ s.card := by
        exact add_le_add
          (mul_le_mul (hf i hi1) hinner (norm_nonneg _) hM0)
          (mul_le_mul (hdiff i hi1) hgnorm (norm_nonneg _) heps)
      _ ≤ ((insert i s).card : ℝ) * eps * M ^ (insert i s).card := by
        rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, pow_succ]
        have hstep : eps * M ^ s.card ≤ (eps * M ^ s.card) * M := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hM
            (mul_nonneg heps (pow_nonneg hM0 _))
        nlinarith


end Erdos821.S56Core
