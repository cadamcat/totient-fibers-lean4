import Erdos821.S56.Definitions

namespace Erdos821.S56
open scoped BigOperators

/-- The triangular dependency of transition phases produces precisely the slot
frequencies in §5; the target contributes only a common scalar phase. -/
theorem slot_frequency_sum (n : ℕ) (target : ℝ) (v s ξ : Fin n → ℝ) (δ : Fin n → Bool) :
    (∑ i, ξ i * (residual target v δ i.val - v i) / s i) =
      target * (∑ i, ξ i / s i) + ∑ t, slotFrequency s ξ δ t * v t := by
  classical
  have hswap :
      (∑ i, (ξ i / s i) * ∑ t ∈ Finset.univ.filter (fun t : Fin n => t.val < i.val),
        if δ t then v t else 0) =
      ∑ t, (if δ t then (1 : ℝ) else 0) * v t *
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => t.val < i.val), ξ i / s i := by
    simp only [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t.val < i.val <;> by_cases hd : δ t = true <;> simp [hi, hd, mul_comm]
  have hfactor : (∑ i, ξ i * (residual target v δ i.val - v i) / s i) =
      ∑ i, (ξ i / s i) * (residual target v δ i.val - v i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfactor]
  simp only [residual, mul_sub, Finset.sum_sub_distrib]
  rw [hswap]
  simp only [slotFrequency, sub_mul, neg_div, neg_mul, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.sum_mul]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring

theorem slot_phase_product (n : ℕ) (target : ℝ) (v s ξ : Fin n → ℝ) (δ : Fin n → Bool) :
    (∏ i, Complex.exp (Complex.I * ((ξ i * (residual target v δ i.val - v i) / s i : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((target * ∑ i, ξ i / s i : ℝ) : ℂ)) *
        ∏ t, Complex.exp (Complex.I * ((slotFrequency s ξ δ t * v t : ℝ) : ℂ)) := by
  have hprod (f : Fin n → ℝ) : (∏ i, Complex.exp (Complex.I * (f i : ℂ))) =
      Complex.exp (Complex.I * ((∑ i, f i : ℝ) : ℂ)) := by
    rw [← Complex.exp_sum]
    congr 1
    simp [Complex.ofReal_sum, Finset.mul_sum]
  rw [hprod, hprod, ← Complex.exp_add, slot_frequency_sum]
  simp only [Complex.ofReal_add, mul_add]


end Erdos821.S56
