import Erdos821.S56.CoreBound

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core

/-- Summing allowable e uses at most tau(u) divisors; no size of E enters. -/
theorem diagonal_fiber_bound (u : ℕ) (hu : 0 < u) (s : Finset ℕ)
    (ah : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ h : ℕ, 0 < h → ‖ah h‖ ≤ M * (h.divisors.card : ℝ)) :
    (∑ e ∈ s, if 0 < e ∧ 2 * e ∣ u then ‖ah (u / (2 * e))‖ ^ 2 else 0) ≤
      M ^ 2 * (u.divisors.card : ℝ) ^ 3 := by
  have hstep (e : ℕ) :
      (if 0 < e ∧ 2 * e ∣ u then ‖ah (u / (2 * e))‖ ^ 2 else 0) ≤
        if e ∈ u.divisors then M ^ 2 * (u.divisors.card : ℝ) ^ 2 else 0 := by
    by_cases he : 0 < e ∧ 2 * e ∣ u
    · have hmem : e ∈ u.divisors := Nat.mem_divisors.mpr
        ⟨(dvd_mul_left e 2).trans he.2, hu.ne'⟩
      have hq : 0 < u / (2 * e) := Nat.div_pos (Nat.le_of_dvd hu he.2) (by omega)
      have hdiv : u / (2 * e) ∣ u := Nat.div_dvd_of_dvd he.2
      have hcard : ((u / (2 * e)).divisors.card : ℝ) ≤ u.divisors.card := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hu.ne' hdiv)
      rw [ite_eq_left he, ite_eq_left hmem]
      have hn := (hh _ hq).trans (mul_le_mul_of_nonneg_left hcard hM)
      calc
        _ ≤ (M * (u.divisors.card : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = _ := by ring
    · rw [ite_eq_right he]
      split_ifs <;> positivity
  calc
    _ ≤ ∑ e ∈ s, if e ∈ u.divisors then M ^ 2 * (u.divisors.card : ℝ) ^ 2 else 0 :=
      Finset.sum_le_sum (fun e _ => hstep e)
    _ = ((s.filter (fun e => e ∈ u.divisors)).card : ℝ) *
        (M ^ 2 * (u.divisors.card : ℝ) ^ 2) := by rw [← Finset.sum_filter]; simp
    _ ≤ (u.divisors.card : ℝ) * (M ^ 2 * (u.divisors.card : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card
        (show s.filter (fun e => e ∈ u.divisors) ⊆ u.divisors from
          fun e he => (Finset.mem_filter.mp he).2)
    _ = _ := by ring

/-- Collecting (m,n) by their product costs exactly its divisor multiplicity. -/
theorem sum_products_le_divisor_sum (s t : Finset ℕ) (N : ℕ) (f : ℕ → ℝ)
    (hf : ∀ v, 0 ≤ f v)
    (hsize : ∀ m ∈ s, ∀ n ∈ t, 0 < m * n ∧ m * n ≤ N) :
    (∑ m ∈ s, ∑ n ∈ t, f (m * n)) ≤
      ∑ v ∈ Finset.Icc 1 N, (v.divisors.card : ℝ) * f v := by
  let q := s ×ˢ t
  have hmap : ∀ p ∈ q, p.1 * p.2 ∈ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hp
    obtain ⟨hpos, hhi⟩ := hsize p.1 hm p.2 hn
    exact Finset.mem_Icc.mpr ⟨hpos, hhi⟩
  have heq := Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2)
    hmap (fun p => f (p.1 * p.2))
  have hprod : (∑ m ∈ s, ∑ n ∈ t, f (m * n)) = ∑ p ∈ q, f (p.1 * p.2) := by
    simp only [q, Finset.sum_product]
  rw [hprod]
  change (∑ p ∈ q, f (p.1 * p.2)) ≤ _
  rw [← heq]
  apply Finset.sum_le_sum
  intro v hv
  have hvpos : 0 < v := (Finset.mem_Icc.mp hv).1
  have hsub : q.filter (fun p : ℕ × ℕ => p.1 * p.2 = v) ⊆ v.divisorsAntidiagonal := by
    intro p hp
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2, hvpos.ne'⟩
  have hc : ((q.filter (fun p : ℕ × ℕ => p.1 * p.2 = v)).card : ℝ) ≤ v.divisors.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (card_divisors_antidiagonal v)
  calc
    _ = ∑ _p ∈ q.filter (fun p : ℕ × ℕ => p.1 * p.2 = v), f v := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = ((q.filter (fun p : ℕ × ℕ => p.1 * p.2 = v)).card : ℝ) * f v := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (hf v)


end Erdos821.S56Core
