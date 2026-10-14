import Erdos821.P8.SieveBasics
import Erdos821.P8.DensityLowerTask
import Erdos821.P8.PrincipalDiscrepancy
import Erdos821.P8.SieveProducts
import Erdos821.P8.DensitySieveLevel

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic SieveBasics

/-- The block sieve applied to ordinary integers has a bounded error at every level. -/
theorem ordinary_rough_dyadic_sieve_upper (hc : ClassicalInputs) (hs : SieveInputs) :
    ∃ K : ℝ, 0 < K ∧ ∃ h0 : ℕ, ∀ h : ℕ, h0 ≤ h → Even h →
      ∀ x z : ℝ, 1 ≤ x → 1 < z →
      (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough z)).card : ℝ) ≤
        x * sieveProduct z * (1 + K * Real.exp (-(h : ℝ))) +
          4 * K * (z ^ (4 * h + 2) + 1) := by
  obtain ⟨KM, hKM⟩ := hc.mertens.1
  have hM : ∀ y : ℝ, 2 ≤ y →
      |reciprocalPrimeSum y - Real.log (Real.log y)| ≤ max KM 0 := by
    intro y hy
    exact (hKM y hy).trans (le_max_left _ _)
  have hKM0 : 0 ≤ max KM 0 := le_max_right _ _
  have hC0 : 0 < 2 * max KM 0 + 10 := by linarith
  obtain ⟨K, hK, h0, hblock⟩ := hs.block (1 / 2) (2 * max KM 0 + 10) (by norm_num) hC0
  refine ⟨K, hK, h0, ?_⟩
  intro h hh heven x z hx hz
  have hx0 : 0 ≤ x := by linarith
  have hx2 : x ≤ 2 * x := by linarith
  let S := apSieveData z x x (2 * x) 1 0 hx0
  have hdb : S.densityBounds z (1 / 2) (2 * max KM 0 + 10) :=
    (apSieve_density_bounds (max KM 0) hM hKM0 z x x (2 * x) 1 0 hx0 hz).2
  have herr := ((hblock ℕ S z hdb).2 h hh heven).1
  have hpr : ∀ p : ℕ, p.Prime → p ∣ 1 → (p : ℝ) ≤ z := by
    intro p hp hpd
    have hp1 := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hpd
    have hp2 := hp.two_le
    omega
  have hcount : S.sifted =
      (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough z)).card : ℝ) := by
    have hraw := apSieve_sifted_count z x (2 * x) 1 0 hx hx2 (by norm_num) (by simp) hpr
    have hXeq : 2 * x - x = x := by ring
    simpa only [Nat.cast_one, div_one, hXeq, Nat.mod_one, eq_self, and_true, S] using hraw
  have hprimes : apSievePrimes z 1 = primesUpTo z := by
    apply Finset.filter_eq_self.mpr
    intro p hp hpd
    have hp1 := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hpd
    have hp2 := (SieveBasics.mem_primesUpTo.mp hp).1.two_le
    omega
  have hproduct : S.product = sieveProduct z := by
    change (∏ p ∈ apSievePrimes z 1, (1 - (p : ℝ)⁻¹)) = sieveProduct z
    rw [hprimes]
    rfl
  have hD : 1 ≤ z ^ (4 * h + 2) := one_le_pow₀ hz.le
  have hrem : S.remainderSum (z ^ (4 * h + 2)) ≤ 4 * (z ^ (4 * h + 2) + 1) := by
    have hraw := apSieve_remainderSum_bound z x (2 * x) 1 0 hx hx2 (by norm_num)
      (z ^ (4 * h + 2)) hD
    have hXeq : 2 * x - x = x := by ring
    simpa only [Nat.cast_one, div_one, hXeq, S] using hraw
  change |S.sifted - x * S.product| ≤
    K * Real.exp (-(h : ℝ)) * x * S.product + K * S.remainderSum (z ^ (4 * h + 2)) at herr
  rw [hcount, hproduct] at herr
  have hupper := (abs_le.mp herr).2
  calc
    _ ≤ x * sieveProduct z + K * Real.exp (-(h : ℝ)) * x * sieveProduct z +
        K * S.remainderSum (z ^ (4 * h + 2)) := by linarith
    _ ≤ x * sieveProduct z + K * Real.exp (-(h : ℝ)) * x * sieveProduct z +
        K * (4 * (z ^ (4 * h + 2) + 1)) := by gcongr
    _ = _ := by ring

lemma tendsto_log_mul_sieveProduct_rpow (hc : ClassicalInputs) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => L x * sieveProduct (x ^ b)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant) / b)) := by
  have hM := hc.mertens.2.comp (tendsto_rpow_atTop hb)
  refine (hM.div_const b).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp, L]
  rw [Real.log_rpow hx]
  field_simp

lemma tendsto_normalized_sieve_remainder (K : ℝ) :
    Tendsto (fun x : ℝ => 4 * K * (L x / x * (x ^ (1 / 4 : ℝ) + 1))) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => L x / x ^ (3 / 4 : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_log_rpow_div_rpow 1 (3 / 4) (by norm_num)
  have h2 : Tendsto (fun x : ℝ => L x / x) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_log_rpow_div_rpow 1 1 (by norm_num)
  have ht : Tendsto (fun x : ℝ => 4 * K * (L x / x ^ (3 / 4 : ℝ) + L x / x))
      atTop (nhds 0) := by simpa only [zero_add, mul_zero] using (h1.add h2).const_mul (4 * K)
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hpow : x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have heq : L x / x * (x ^ (1 / 4 : ℝ) + 1) = L x / x ^ (3 / 4 : ℝ) + L x / x := by
    field_simp
    linear_combination (L x) * hpow
  rw [heq]

lemma roughDensity_le_of_count_upper (hc : ClassicalInputs)
    (hlower : RoughDyadicDensityLowerTask) (b : ℝ) (hb : 0 < b) (hb1 : b < 1)
    (F : ℝ → ℝ) (y : ℝ) (hF : Tendsto F atTop (nhds y))
    (hupper : ∀ᶠ x : ℝ in atTop, L x / x *
      (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b))).card : ℝ) ≤ F x) :
    roughDensity b 1 ≤ y := by
  apply le_of_forall_pos_le_add
  intro eps heps
  have hbelow : ∀ᶠ x : ℝ in atTop, roughDensity b 1 - eps ≤ F x := by
    filter_upwards [hlower hc b hb hb1 eps heps, hupper] with x hx hu
    exact hx.trans hu
  have hlim := ge_of_tendsto hF hbelow
  linarith

/-- The lower ordinary count limit and the block sieve imply the density sieve upper field. -/
theorem density_sieve_upper_from_lower (hc : ClassicalInputs) (hs : SieveInputs)
    (hlower : RoughDyadicDensityLowerTask) :
    ∃ c K b0 : ℝ, 0 < c ∧ 0 < K ∧ 0 < b0 ∧ ∀ b : ℝ, 0 < b → b < b0 →
      roughDensity b 1 ≤ Real.exp (-Real.eulerMascheroniConstant) / b *
        (1 + K * Real.exp (-c / b)) := by
  obtain ⟨K, hK, h0, hupper⟩ := ordinary_rough_dyadic_sieve_upper hc hs
  refine ⟨1 / 20, K * Real.exp 2,
    min (1 / 100 : ℝ) (1 / (40 * ((h0 : ℝ) + 2))), by norm_num, by positivity, by positivity, ?_⟩
  intro b hb hbsmall
  rcases dyadicSieveLevel_bounds h0 hb hbsmall with ⟨hh, heven, hexp, _hlevelLo⟩
  let h := dyadicSieveLevel b
  let F : ℝ → ℝ := fun x =>
    (1 + K * Real.exp (-(h : ℝ))) * (L x * sieveProduct (x ^ b)) +
      4 * K * (L x / x * (x ^ (1 / 4 : ℝ) + 1))
  have hb1 : b < 1 := (hbsmall.trans_le (min_le_left _ _)).trans (by norm_num)
  have hF : Tendsto F atTop (nhds (Real.exp (-Real.eulerMascheroniConstant) / b *
      (1 + K * Real.exp (-(h : ℝ))))) := by
    simpa only [F, add_zero, mul_comm] using
      ((tendsto_log_mul_sieveProduct_rpow hc b hb).const_mul
        (1 + K * Real.exp (-(h : ℝ)))).add (tendsto_normalized_sieve_remainder K)
  have hcountUpper : ∀ᶠ x : ℝ in atTop, L x / x *
      (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b))).card : ℝ) ≤ F x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hL0 : 0 < L x := Real.log_pos hx
    have hz : 1 < x ^ b := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_lt_rpow_of_exponent_lt hx hb : x ^ (0 : ℝ) < x ^ b)
    have hraw := hupper h hh heven x (x ^ b) hx.le hz
    have hD : (x ^ b) ^ (4 * h + 2) ≤ x ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow_of_exponent_le hx.le hexp
    have hscaled := mul_le_mul_of_nonneg_left hraw (div_nonneg hL0.le hx0.le)
    calc
      _ ≤ L x / x * (x * sieveProduct (x ^ b) * (1 + K * Real.exp (-(h : ℝ))) +
          4 * K * ((x ^ b) ^ (4 * h + 2) + 1)) := hscaled
      _ ≤ L x / x * (x * sieveProduct (x ^ b) * (1 + K * Real.exp (-(h : ℝ))) +
          4 * K * (x ^ (1 / 4 : ℝ) + 1)) := by gcongr
      _ = F x := by dsimp [F]; field_simp
  have hdensity := roughDensity_le_of_count_upper hc hlower b hb hb1 F _ hF hcountUpper
  have hExp := dyadicSieveLevel_exp_upper h0 hb hbsmall
  have hconstant : 1 + K * Real.exp (-(h : ℝ)) ≤
      1 + (K * Real.exp 2) * Real.exp (-(1 / 20 : ℝ) / b) := by
    have := mul_le_mul_of_nonneg_left hExp hK.le
    dsimp [h] at this ⊢
    nlinarith
  exact hdensity.trans (mul_le_mul_of_nonneg_left hconstant (by positivity))

end Erdos821.P8Core

