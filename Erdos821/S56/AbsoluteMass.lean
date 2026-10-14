import Erdos821.S56.DiagonalMoments
import Erdos821.S56.WeightBound

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def divisorPairMass (U V : ℝ) : ℝ :=
  ∑ m ∈ dyad U, ∑ n ∈ dyad V,
    if Odd (m*n) ∧ 1 < m*n then (((m*n-1)/2).divisors.card : ℝ) else 0

/-- The absolute mass needed for Fourier errors costs only ordinary divisor
moments. The odd-product gate ensures that every shifted argument is positive. -/
theorem divisor_pair_mass_bound (x U V : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUV : U*V ≤ 8*x) :
    divisorPairMass U V ≤ ∑ v ∈ Finset.Icc 1 ⌊64*x⌋₊,
      (v.divisors.card : ℝ)*((v-1).divisors.card : ℝ)^3 := by
  have hpoint (m n : ℕ) :
      (if Odd (m*n) ∧ 1 < m*n then (((m*n-1)/2).divisors.card : ℝ) else 0) ≤
        ((m*n-1).divisors.card : ℝ)^3 := by
    split_ifs with h
    · have hv : 0 < m*n-1 := by omega
      obtain ⟨k, hk⟩ := h.1
      have h2 : 2 ∣ m*n-1 := ⟨k, by omega⟩
      have hd := Nat.div_dvd_of_dvd h2
      have hcard : (((m*n-1)/2).divisors.card : ℝ) ≤ (m*n-1).divisors.card := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hv.ne' hd)
      have hnonempty := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hv.ne'⟩
      have hc1 : (1:ℝ) ≤ (m*n-1).divisors.card := by exact_mod_cast hnonempty
      apply hcard.trans
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg ((m*n-1).divisors.card : ℝ)),
        mul_nonneg (by linarith : (0:ℝ) ≤ (m*n-1).divisors.card) (sub_nonneg.mpr hc1)]
    · positivity
  have hsize : ∀ m ∈ dyad U, ∀ n ∈ dyad V, 0 < m*n ∧ m*n ≤ ⌊64*x⌋₊ := by
    intro m hm n hn
    have hmlo := Nat.ceil_le.mp (Finset.mem_Ico.mp hm).1
    have hnlo := Nat.ceil_le.mp (Finset.mem_Ico.mp hn).1
    have hmhi := Nat.lt_ceil.mp (Finset.mem_Ico.mp hm).2
    have hnhi := Nat.lt_ceil.mp (Finset.mem_Ico.mp hn).2
    have hmpos : 0 < m := by exact_mod_cast (zero_lt_one.trans_le (hU.trans hmlo))
    have hnpos : 0 < n := by exact_mod_cast (zero_lt_one.trans_le (hV.trans hnlo))
    refine ⟨mul_pos hmpos hnpos, Nat.le_floor ?_⟩
    push_cast
    have hp := mul_le_mul hmhi.le hnhi.le (Nat.cast_nonneg n : (0:ℝ) ≤ n) (by linarith : 0 ≤ 2*U)
    nlinarith
  calc
    _ ≤ ∑ m ∈ dyad U, ∑ n ∈ dyad V, ((m*n-1).divisors.card : ℝ)^3 :=
      Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => hpoint m n))
    _ ≤ _ := sum_products_le_divisor_sum (dyad U) (dyad V) ⌊64*x⌋₊
      (fun v => ((v-1).divisors.card : ℝ)^3) (fun _ => by positivity) hsize

theorem divisor_pair_mass_polylog (hc : ClassicalInputs) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ U V : ℝ,
      1 ≤ U → 1 ≤ V → U*V ≤ 8*x → divisorPairMass U V ≤ K*x*L x^C := by
  obtain ⟨C, K, hC, hK, hm⟩ := divisor_shifted_polylog hc
  refine ⟨C, K, hC, hK, ?_⟩
  filter_upwards [hm] with x hx
  intro U V hU hV hUV
  exact (divisor_pair_mass_bound x U V hU hV hUV).trans hx

def weightedPairMass (D : BandData) (x : ℝ) (jstar : ℕ) (U V : ℝ) : ℝ :=
  ∑ m ∈ dyad U, ∑ n ∈ dyad V,
    if Odd (m*n) ∧ 1 < m*n then D.weight x jstar ((m*n-1)/2) else 0

/-- Summing an absolute pre-Cauchy Fourier error costs a fixed log power,
uniformly in U,V. The exceptional band is fixed before the eventual x bound. -/
theorem weighted_pair_mass_polylog (hc : ClassicalInputs) (D : BandData) (hD : D.Valid) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop, ∀ U V : ℝ,
      1 ≤ U → 1 ≤ V → U*V ≤ 8*x → weightedPairMass D x jstar U V ≤ K*x*L x^C := by
  obtain ⟨Cw, hCw, hw⟩ := band_weight_divisor_bound D hD
  obtain ⟨Cp, K, hCp, hK, hp⟩ := divisor_pair_mass_polylog hc
  refine ⟨Cw+Cp, K, by positivity, hK, ?_⟩
  intro jstar
  filter_upwards [hw jstar, hp, tendsto_L.eventually (eventually_gt_atTop 0)] with x hw hp hL
  intro U V hU hV hUV
  have hraw : weightedPairMass D x jstar U V ≤ L x^Cw*divisorPairMass U V := by
    simp only [weightedPairMass, divisorPairMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    apply Finset.sum_le_sum
    intro n _
    split_ifs with h
    · have hu : 0 < (m*n-1)/2 := by
        obtain ⟨k, hk⟩ := h.1
        omega
      exact hw _ hu
    · simp
  calc
    _ ≤ _ := hraw
    _ ≤ L x^Cw*(K*x*L x^Cp) :=
      mul_le_mul_of_nonneg_left (hp U V hU hV hUV) (by positivity)
    _ = _ := by rw [Real.rpow_add hL]; ring


end Erdos821.S56Core
