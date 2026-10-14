import Erdos821.S56.DiagonalMoments
import Erdos821.S56.Cauchy

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def diagonalSum (E U V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
    etae (e / E) * etan (n / V) *
      ∑ m ∈ dyad U, if 1 < m * n ∧ 2 * e ∣ m * n - 1 then
        ‖alpha m * ah ((m * n - 1) / (2 * e))‖ ^ 2 else 0

theorem diagonal_sum_bound (x E U V M : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U * V ≤ 8 * x)
    (hM : 0 ≤ M) (he : ∀ y, 0 ≤ etae y ∧ etae y ≤ 1)
    (hn : ∀ y, 0 ≤ etan y ∧ etan y ≤ 1)
    (halpha : ∀ m, ‖alpha m‖ ≤ M)
    (hah : ∀ h : ℕ, 0 < h → ‖ah h‖ ≤ M * (h.divisors.card : ℝ)) :
    diagonalSum E U V etae etan ah alpha ≤ M ^ 4 *
      ∑ v ∈ Finset.Icc 1 ⌊64 * x⌋₊,
        (v.divisors.card : ℝ) * ((v - 1).divisors.card : ℝ) ^ 3 := by
  let se := Finset.Icc 1 ⌊2 * E⌋₊
  let sn := Finset.Icc 1 ⌊4 * V⌋₊
  let sm := dyad U
  let term : ℕ → ℕ → ℕ → ℝ := fun e n m =>
    if 1 < m * n ∧ 2 * e ∣ m * n - 1 then
      ‖alpha m * ah ((m * n - 1) / (2 * e))‖ ^ 2 else 0
  have hterm (e n m : ℕ) : 0 ≤ term e n m := by dsimp [term]; split_ifs <;> positivity
  have hdrop : diagonalSum E U V etae etan ah alpha ≤ ∑ e ∈ se, ∑ n ∈ sn, ∑ m ∈ sm, term e n m := by
    apply Finset.sum_le_sum
    intro e _
    apply Finset.sum_le_sum
    intro n _
    have hw : etae (e / E) * etan (n / V) ≤ 1 := by
      have h := mul_le_mul (he ((e : ℝ) / E)).2 (hn ((n : ℝ) / V)).2
        (hn ((n : ℝ) / V)).1 (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using h
    have hs0 : 0 ≤ ∑ m ∈ sm, term e n m := Finset.sum_nonneg (fun m _ => hterm e n m)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw hs0
  have hreorder : (∑ e ∈ se, ∑ n ∈ sn, ∑ m ∈ sm, term e n m) =
      ∑ m ∈ sm, ∑ n ∈ sn, ∑ e ∈ se, term e n m := by
    calc
      _ = ∑ n ∈ sn, ∑ e ∈ se, ∑ m ∈ sm, term e n m := Finset.sum_comm
      _ = ∑ n ∈ sn, ∑ m ∈ sm, ∑ e ∈ se, term e n m :=
        Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have hfiber (m n : ℕ) : (∑ e ∈ se, term e n m) ≤
      M ^ 4 * ((m * n - 1).divisors.card : ℝ) ^ 3 := by
    by_cases hmn : 1 < m * n
    · have hu : 0 < m * n - 1 := by omega
      have hsep : (∑ e ∈ se, term e n m) = ‖alpha m‖ ^ 2 *
          ∑ e ∈ se, if 0 < e ∧ 2 * e ∣ m * n - 1 then
            ‖ah ((m * n - 1) / (2 * e))‖ ^ 2 else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        have hepos : 0 < e := (Finset.mem_Icc.mp he).1
        by_cases hd : 2 * e ∣ m * n - 1 <;> simp [term, hmn, hd, hepos, norm_mul, mul_pow]
      rw [hsep]
      have ha2 := pow_le_pow_left₀ (norm_nonneg (alpha m)) (halpha m) 2
      have hdiv := diagonal_fiber_bound _ hu se ah M hM hah
      have hs0 : 0 ≤ ∑ e ∈ se, if 0 < e ∧ 2 * e ∣ m * n - 1 then
          ‖ah ((m * n - 1) / (2 * e))‖ ^ 2 else 0 := by
        apply Finset.sum_nonneg
        intro e _
        split_ifs <;> positivity
      have h := mul_le_mul ha2 hdiv hs0 (pow_nonneg hM 2)
      convert h using 1 <;> ring
    · have hz : (∑ e ∈ se, term e n m) = 0 := by simp [term, hmn]
      rw [hz]
      positivity
  have hsize : ∀ m ∈ sm, ∀ n ∈ sn, 0 < m * n ∧ m * n ≤ ⌊64 * x⌋₊ := by
    intro m hm n hn
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ico.mp hm
    have hmL : U ≤ (m : ℝ) := Nat.ceil_le.mp hmlo
    have hmH : (m : ℝ) < 2 * U := Nat.lt_ceil.mp hmhi
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    have hnH : (n : ℝ) ≤ 4 * V := (Nat.le_floor_iff (by linarith : 0 ≤ 4 * V)).mp hnhi
    have hmpos : 0 < m := by exact_mod_cast (zero_lt_one.trans_le (hU.trans hmL))
    refine ⟨mul_pos hmpos hnlo, ?_⟩
    apply Nat.le_floor
    push_cast
    have hprod := mul_le_mul hmH.le hnH (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      (by linarith : 0 ≤ 2 * U)
    nlinarith
  have hprod := sum_products_le_divisor_sum sm sn ⌊64 * x⌋₊
    (fun v => ((v - 1).divisors.card : ℝ) ^ 3) (fun v => by positivity) hsize
  calc
    _ ≤ _ := hdrop
    _ = _ := hreorder
    _ ≤ ∑ m ∈ sm, ∑ n ∈ sn, M ^ 4 * ((m * n - 1).divisors.card : ℝ) ^ 3 :=
      Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => hfiber m n))
    _ = M ^ 4 * ∑ m ∈ sm, ∑ n ∈ sn, ((m * n - 1).divisors.card : ℝ) ^ 3 := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (pow_nonneg hM 4)


/-- All diagonal logarithmic costs are fixed before choosing K₀. -/
theorem diagonal_polylog (hc : ClassicalInputs) (C : ℝ) (hC : 0 ≤ C) :
    ∃ C' K : ℝ, 0 < C' ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (E U V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ),
        1 ≤ U → 1 ≤ V → U * V ≤ 8 * x →
        (∀ y, 0 ≤ etae y ∧ etae y ≤ 1) → (∀ y, 0 ≤ etan y ∧ etan y ≤ 1) →
        (∀ m, ‖alpha m‖ ≤ L x ^ C) →
        (∀ h : ℕ, 0 < h → ‖ah h‖ ≤ L x ^ C * (h.divisors.card : ℝ)) →
        diagonalSum E U V etae etan ah alpha ≤ K * x * L x ^ C' := by
  obtain ⟨Cd, K, hCd, hK, hdiag⟩ := divisor_shifted_polylog hc
  refine ⟨4 * C + Cd, K, by positivity, hK, ?_⟩
  filter_upwards [hdiag, tendsto_L.eventually (eventually_gt_atTop 0)] with x hx hL
  intro E U V etae etan ah alpha hU hV hUV he hn halpha hah
  have hbound := diagonal_sum_bound x E U V (L x ^ C) etae etan ah alpha hU hV hUV
    (Real.rpow_nonneg hL.le _) he hn halpha hah
  have hp : (L x ^ C) ^ (4 : ℕ) = L x ^ (4 * C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    ring
  calc
    _ ≤ _ := hbound
    _ ≤ (L x ^ C) ^ (4 : ℕ) * (K * x * L x ^ Cd) :=
      mul_le_mul_of_nonneg_left hx (pow_nonneg (Real.rpow_nonneg hL.le _) _)
    _ = K * x * L x ^ (4 * C + Cd) := by
      rw [hp, Real.rpow_add hL]
      ring


end Erdos821.S56Core
