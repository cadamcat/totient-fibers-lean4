import Erdos821.S56.DiagonalFibers
import Erdos821.P6Sq.EndpointSquareTask
import Erdos821.S56.BandSize

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem shifted_divisor_moment_le (N k : ℕ) (hk : 0 < k) :
    (∑ v ∈ Finset.Icc 1 N, (((v - 1).divisors.card : ℝ) ^ k)) ≤
      ∑ v ∈ Finset.Icc 1 N, (v.divisors.card : ℝ) ^ k := by
  let s := (Finset.Icc 1 N).filter (fun v => 1 < v)
  have heq : (∑ v ∈ Finset.Icc 1 N, (((v - 1).divisors.card : ℝ) ^ k)) =
      ∑ v ∈ s, (((v - 1).divisors.card : ℝ) ^ k) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : 1 < v
    · rw [ite_eq_left h]
    · have hv1 : v = 1 := by obtain ⟨hvlo, hvhi⟩ := Finset.mem_Icc.mp hv; omega
      subst v
      simp [hk.ne']
  have hinj : Set.InjOn (fun v : ℕ => v - 1) s := by
    intro v hv w hw h
    have hv1 := (Finset.mem_filter.mp hv).2
    have hw1 := (Finset.mem_filter.mp hw).2
    dsimp only at h
    omega
  have hsub : s.image (fun v => v - 1) ⊆ Finset.Icc 1 N := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hvN, hv1⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvlo, hvhi⟩ := Finset.mem_Icc.mp hvN
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [heq]
  calc
    _ = ∑ w ∈ s.image (fun v => v - 1), (w.divisors.card : ℝ) ^ k := by
      rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => by positivity)

theorem divisor_product_moment_le (N : ℕ) :
    (∑ v ∈ Finset.Icc 1 N, (v.divisors.card : ℝ) * ((v - 1).divisors.card : ℝ) ^ 3) ≤
      (∑ v ∈ Finset.Icc 1 N, (v.divisors.card : ℝ) ^ 2) +
        ∑ v ∈ Finset.Icc 1 N, (v.divisors.card : ℝ) ^ 6 := by
  calc
    _ ≤ ∑ v ∈ Finset.Icc 1 N,
        ((v.divisors.card : ℝ) ^ 2 + ((v - 1).divisors.card : ℝ) ^ 6) := by
      apply Finset.sum_le_sum
      intro v _
      nlinarith [sq_nonneg ((v.divisors.card : ℝ) - ((v - 1).divisors.card : ℝ) ^ 3),
        sq_nonneg (v.divisors.card : ℝ), sq_nonneg (((v - 1).divisors.card : ℝ) ^ 3)]
    _ = (∑ v ∈ Finset.Icc 1 N, (v.divisors.card : ℝ) ^ 2) +
        ∑ v ∈ Finset.Icc 1 N, ((v - 1).divisors.card : ℝ) ^ 6 := Finset.sum_add_distrib
    _ ≤ _ := add_le_add le_rfl (shifted_divisor_moment_le N 6 (by norm_num))

/-- The ordinary divisor moments give the diagonal's shifted product bound.
Its exponent is fixed before E and the splitting precision K₀. -/
theorem divisor_shifted_polylog (hc : ClassicalInputs) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ v ∈ Finset.Icc 1 ⌊64 * x⌋₊,
        (v.divisors.card : ℝ) * ((v - 1).divisors.card : ℝ) ^ 3) ≤ K * x * L x ^ C := by
  obtain ⟨A2, K2, hK2, hm2⟩ := hc.divisors 2
  obtain ⟨A6, K6, hK6, hm6⟩ := hc.divisors 6
  let M2 := Erdos821.P6Sq.momentLogFactor A2
  let M6 := Erdos821.P6Sq.momentLogFactor A6
  let C := max (max A2 0) (max A6 0) + 1
  let K := 64 * (K2 * M2 + K6 * M6)
  have hM2 : 0 < M2 := by dsimp [M2, Erdos821.P6Sq.momentLogFactor]; positivity
  have hM6 : 0 < M6 := by dsimp [M6, Erdos821.P6Sq.momentLogFactor]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, K, hC, hK, ?_⟩
  filter_upwards [eventually_ge_atTop 64, tendsto_L.eventually (eventually_ge_atTop 3)] with x hx hL
  have hxpos : 0 < x := by linarith
  have hY : 1 ≤ 64 * x := by linarith
  have hYx : 64 * x ≤ x ^ (2 : ℕ) := by nlinarith
  have hl2 := Erdos821.P6Sq.logMoment_majorant x (64 * x) A2 (by linarith) hL hY hYx
  have hl6 := Erdos821.P6Sq.logMoment_majorant x (64 * x) A6 (by linarith) hL hY hYx
  have hC2 : max A2 0 ≤ C := by dsimp [C]; linarith [le_max_left (max A2 0) (max A6 0)]
  have hC6 : max A6 0 ≤ C := by dsimp [C]; linarith [le_max_right (max A2 0) (max A6 0)]
  have hp2 := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L x) hC2
  have hp6 := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L x) hC6
  have h2 : (∑ v ∈ Finset.Icc 1 ⌊64 * x⌋₊, (v.divisors.card : ℝ) ^ 2) ≤
      K2 * (64 * x) * (M2 * L x ^ C) :=
    (hm2 _ hY).2.trans (mul_le_mul_of_nonneg_left
      (hl2.trans (mul_le_mul_of_nonneg_left hp2 hM2.le)) (by positivity))
  have h6 : (∑ v ∈ Finset.Icc 1 ⌊64 * x⌋₊, (v.divisors.card : ℝ) ^ 6) ≤
      K6 * (64 * x) * (M6 * L x ^ C) :=
    (hm6 _ hY).2.trans (mul_le_mul_of_nonneg_left
      (hl6.trans (mul_le_mul_of_nonneg_left hp6 hM6.le)) (by positivity))
  calc
    _ ≤ _ := divisor_product_moment_le _
    _ ≤ K2 * (64 * x) * (M2 * L x ^ C) + K6 * (64 * x) * (M6 * L x ^ C) := add_le_add h2 h6
    _ = _ := by dsimp [K]; ring


end Erdos821.S56Core
