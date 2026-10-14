import Erdos821.S9.EulerTasks

noncomputable section

open scoped BigOperators
open Filter

namespace Erdos821.S9Div

lemma pairDComp_le_one_add_sixteen_div (p D : ℕ) (hp : 2 ≤ p) (hpd : p ∣ D) :
    Erdos821.P9Core.pairDComp p D ≤ 1 + 16 / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by positivity
  have hpR2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  have hpRm1 : 0 < (p : ℝ) - 1 := by linarith
  have hbase : 0 < 1 - 1 / (p : ℝ) := by
    have hfrac : 1 / (p : ℝ) < 1 := (div_lt_one hpR).2 (by linarith)
    linarith
  have hratio : (p : ℝ) / ((p : ℝ) - 1) ≤ 1 + 2 / (p : ℝ) := by
    rw [div_le_iff₀ hpRm1]
    field_simp [ne_of_gt hpR]
    nlinarith
  have hratio3 : ((p : ℝ) / ((p : ℝ) - 1)) ^ 3 ≤
      (1 + 2 / (p : ℝ)) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) hratio 3
  have hcube : (1 + 2 / (p : ℝ)) ^ 3 ≤ 1 + 16 / (p : ℝ) := by
    have hp2sq : 0 < (p : ℝ) ^ 2 := by positivity
    have hp2cube : 0 < (p : ℝ) ^ 3 := by positivity
    field_simp [ne_of_gt hpR]
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hidentity : ((1 - 1 / (p : ℝ)) ^ 3)⁻¹ =
      ((p : ℝ) / ((p : ℝ) - 1)) ^ 3 := by
    field_simp [ne_of_gt hpR, ne_of_gt hpRm1, ne_of_gt hbase]
    <;> ring
  rw [Erdos821.P9Core.pairDComp, if_pos hpd, hidentity]
  exact hratio3.trans hcube

lemma divisorCompensation_product_bound (x : ℝ) (D : ℕ) (z : ℝ)
    (hx : 0 < x) (hL : 2 ≤ Erdos821.Blueprint.Analytic.L x) (hD : 0 < D)
    (hDsmall : (D : ℝ) ≤ x ^ (1 / 20 : ℝ))
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ D →
      Erdos821.Blueprint.Analytic.L x ^ (20 : ℕ) ≤ (p : ℝ)) :
    (∏ p ∈ Erdos821.Blueprint.primesUpTo z, Erdos821.P9Core.pairDComp p D) ≤
      Real.exp (16 / Real.log 2) := by
  classical
  let Y : ℝ := Erdos821.Blueprint.Analytic.L x ^ (20 : ℕ)
  let c : ℝ := Real.log 2
  let S : Finset ℕ := (Erdos821.Blueprint.primesUpTo z).filter (fun p => p ∣ D)
  let F : ℕ → ℝ := fun p => ((1 - 1 / (p : ℝ)) ^ 3)⁻¹
  have hc : 0 < c := by
    dsimp [c]
    exact Real.log_pos (by norm_num)
  have hLpos : 0 < Erdos821.Blueprint.Analytic.L x := by linarith
  have hLone : 1 ≤ Erdos821.Blueprint.Analytic.L x := by linarith
  have hpow19 : 1 ≤ Erdos821.Blueprint.Analytic.L x ^ (19 : ℕ) := by
    calc
      1 = (1 : ℝ) ^ (19 : ℕ) := by norm_num
      _ ≤ Erdos821.Blueprint.Analytic.L x ^ (19 : ℕ) := by gcongr
  have hLY : Erdos821.Blueprint.Analytic.L x ≤ Y := by
    dsimp [Y]
    calc
      Erdos821.Blueprint.Analytic.L x = 1 * Erdos821.Blueprint.Analytic.L x := by ring
      _ ≤ Erdos821.Blueprint.Analytic.L x ^ (19 : ℕ) * Erdos821.Blueprint.Analytic.L x :=
        mul_le_mul_of_nonneg_right hpow19 hLpos.le
      _ = Erdos821.Blueprint.Analytic.L x ^ (20 : ℕ) := by ring
  have hY2 : 2 ≤ Y := hL.trans hLY
  have hYpos : 0 < Y := by linarith
  have hSsubset : S ⊆ D.primeFactors := by
    intro p hpS
    have hpQ : p ∈ Erdos821.Blueprint.primesUpTo z := (Finset.mem_filter.mp hpS).1
    have hpD : p ∣ D := (Finset.mem_filter.mp hpS).2
    have hpPrime : p.Prime := by
      change p ∈ (Finset.Icc 1 ⌊z⌋₊).filter Nat.Prime at hpQ
      exact (Finset.mem_filter.mp hpQ).2
    exact (Nat.mem_primeFactors_of_ne_zero hD.ne').2 ⟨hpPrime, hpD⟩
  have hfactor_eq :
      (∏ p ∈ Erdos821.Blueprint.primesUpTo z, Erdos821.P9Core.pairDComp p D) =
        ∏ p ∈ S, F p := by
    dsimp [S, F, Erdos821.P9Core.pairDComp]
    rw [← Finset.prod_filter]
  have hFnonneg : ∀ p ∈ S, 0 ≤ F p := by
    intro p hpS
    have hpPrime : p.Prime := by
      have hpQ : p ∈ Erdos821.Blueprint.primesUpTo z := (Finset.mem_filter.mp hpS).1
      change p ∈ (Finset.Icc 1 ⌊z⌋₊).filter Nat.Prime at hpQ
      exact (Finset.mem_filter.mp hpQ).2
    have hpR2 : 2 ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
    have hpR : 0 < (p : ℝ) := by positivity
    have hbase : 0 < 1 - 1 / (p : ℝ) := by
      have hfrac : 1 / (p : ℝ) < 1 := (div_lt_one hpR).2 (by linarith)
      linarith
    dsimp [F]
    positivity
  have hFle : ∀ p ∈ S, F p ≤ 1 + 16 / (p : ℝ) := by
    intro p hpS
    have hpD : p ∣ D := (Finset.mem_filter.mp hpS).2
    have hpQ : p ∈ Erdos821.Blueprint.primesUpTo z := (Finset.mem_filter.mp hpS).1
    have hpPrime : p.Prime := by
      change p ∈ (Finset.Icc 1 ⌊z⌋₊).filter Nat.Prime at hpQ
      exact (Finset.mem_filter.mp hpQ).2
    have hp2 : 2 ≤ p := hpPrime.two_le
    simpa [F, Erdos821.P9Core.pairDComp, hpD] using
      pairDComp_le_one_add_sixteen_div p D hp2 hpD
  have hlocalProd : (∏ p ∈ S, F p) ≤ ∏ p ∈ S, (1 + 16 / (p : ℝ)) :=
    Finset.prod_le_prod₀ hFnonneg hFle
  have hrecip : ∀ p ∈ S, 1 / (p : ℝ) ≤
      Real.log (p : ℝ) / (c * Y) := by
    intro p hpS
    have hpQ : p ∈ Erdos821.Blueprint.primesUpTo z := (Finset.mem_filter.mp hpS).1
    have hpD : p ∣ D := (Finset.mem_filter.mp hpS).2
    have hpPrime : p.Prime := by
      change p ∈ (Finset.Icc 1 ⌊z⌋₊).filter Nat.Prime at hpQ
      exact (Finset.mem_filter.mp hpQ).2
    have hpY : Y ≤ (p : ℝ) := hlarge p hpPrime hpD
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := hY2.trans hpY
    have hlog2 : c ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) hp2
    have hlogp : 0 ≤ Real.log (p : ℝ) := le_trans hc.le hlog2
    have hpR : 0 < (p : ℝ) := by positivity
    have hden : 0 < c * Y := mul_pos hc hYpos
    have hcross : c * Y ≤ Real.log (p : ℝ) * (p : ℝ) :=
      mul_le_mul hlog2 hpY hYpos.le hlogp
    rw [div_le_div_iff₀ hpR hden]
    nlinarith [hcross]
  have hprodNatDvd : (∏ p ∈ S, p) ∣ D :=
    dvd_trans (Finset.prod_dvd_prod_of_subset S D.primeFactors id hSsubset)
      (Nat.prod_primeFactors_dvd D)
  have hprodNatPos : 0 < ∏ p ∈ S, p := by
    apply Finset.prod_pos
    intro p hpS
    have hpPrime := (Nat.mem_primeFactors_of_ne_zero hD.ne').1 (hSsubset hpS) |>.1
    exact hpPrime.pos
  have hprodNatLe : (∏ p ∈ S, p) ≤ D := Nat.le_of_dvd hD hprodNatDvd
  have hcastProd : (∏ p ∈ S, (p : ℝ)) = ((∏ p ∈ S, p : ℕ) : ℝ) := by
    simp [Nat.cast_prod]
  have hlogProd : Real.log (∏ p ∈ S, (p : ℝ)) =
      ∑ p ∈ S, Real.log (p : ℝ) := by
    apply Real.log_prod
    intro p hpS
    have hpPrime := (Nat.mem_primeFactors_of_ne_zero hD.ne').1 (hSsubset hpS) |>.1
    exact_mod_cast hpPrime.ne_zero
  have hlogNatProd : (∑ p ∈ S, Real.log (p : ℝ)) =
      Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by
    calc
      (∑ p ∈ S, Real.log (p : ℝ)) = Real.log (∏ p ∈ S, (p : ℝ)) := hlogProd.symm
      _ = Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by rw [hcastProd]
  have hlogD : Real.log (D : ℝ) ≤ Erdos821.Blueprint.Analytic.L x / 20 := by
    calc
      Real.log (D : ℝ) ≤ Real.log (x ^ (1 / 20 : ℝ)) :=
        Real.log_le_log (Nat.cast_pos.mpr hD) hDsmall
      _ = Erdos821.Blueprint.Analytic.L x / 20 := by
        rw [Real.rpow_def_of_pos hx, Real.log_exp]
        simp [Erdos821.Blueprint.Analytic.L, div_eq_mul_inv, mul_comm]
  have hlogProdLe : Real.log (∏ p ∈ S, (p : ℝ)) ≤
      Erdos821.Blueprint.Analytic.L x / 20 := by
    rw [hcastProd]
    calc
      Real.log ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Real.log (D : ℝ) :=
        Real.log_le_log (Nat.cast_pos.mpr hprodNatPos) (by exact_mod_cast hprodNatLe)
      _ ≤ Erdos821.Blueprint.Analytic.L x / 20 := hlogD
  have hsumLog : (∑ p ∈ S, Real.log (p : ℝ)) ≤
      Erdos821.Blueprint.Analytic.L x / 20 := by
    rw [← hlogProd]
    exact hlogProdLe
  have hsumComp : (∑ p ∈ S, 16 / (p : ℝ)) ≤
      (16 / (c * Y)) * (Erdos821.Blueprint.Analytic.L x / 20) := by
    calc
      (∑ p ∈ S, 16 / (p : ℝ)) ≤
          ∑ p ∈ S, (16 / (c * Y)) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hpS
        calc
          16 / (p : ℝ) = 16 * (1 / (p : ℝ)) := by ring
          _ ≤ 16 * (Real.log (p : ℝ) / (c * Y)) :=
            mul_le_mul_of_nonneg_left (hrecip p hpS) (by norm_num)
          _ = (16 / (c * Y)) * Real.log (p : ℝ) := by ring
      _ = (16 / (c * Y)) * ∑ p ∈ S, Real.log (p : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ (16 / (c * Y)) * (Erdos821.Blueprint.Analytic.L x / 20) :=
        mul_le_mul_of_nonneg_left hsumLog (by positivity)
  have hLdiv : Erdos821.Blueprint.Analytic.L x / (20 * Y) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith [hLY]
  have hsumComp' : (∑ p ∈ S, 16 / (p : ℝ)) ≤ 16 / c := by
    calc
      (∑ p ∈ S, 16 / (p : ℝ)) ≤
          (16 / (c * Y)) * (Erdos821.Blueprint.Analytic.L x / 20) := hsumComp
      _ = (16 / c) * (Erdos821.Blueprint.Analytic.L x / (20 * Y)) := by
        field_simp [ne_of_gt hc, ne_of_gt hYpos]
        <;> ring
      _ ≤ (16 / c) * 1 := mul_le_mul_of_nonneg_left hLdiv (by positivity)
      _ = 16 / c := by ring
  have hsmallProd : (∏ p ∈ S, (1 + 16 / (p : ℝ))) ≤
      Real.exp (∑ p ∈ S, 16 / (p : ℝ)) :=
    Real.prod_one_add_le_exp_sum S (fun p => by positivity)
  rw [hfactor_eq]
  calc
    (∏ p ∈ S, F p) ≤ ∏ p ∈ S, (1 + 16 / (p : ℝ)) := hlocalProd
    _ ≤ Real.exp (∑ p ∈ S, 16 / (p : ℝ)) := hsmallProd
    _ ≤ Real.exp (16 / c) := Real.exp_le_exp.mpr hsumComp'

theorem divisorCompensationTask_proof : Erdos821.S56Core.DivisorCompensationTask := by
  let c : ℝ := Real.log 2
  let K : ℝ := Real.exp (16 / c)
  have hc : 0 < c := by
    dsimp [c]
    exact Real.log_pos (by norm_num)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  have hlogEventually : ∀ᶠ x : ℝ in atTop, 2 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  have hxEventually : ∀ᶠ x : ℝ in atTop, 0 < x :=
    eventually_gt_atTop 0
  filter_upwards [hlogEventually, hxEventually] with x hlog hx
  intro D z hD hDsmall hlarge
  have hL : 2 ≤ Erdos821.Blueprint.Analytic.L x := by
    simpa [Erdos821.Blueprint.Analytic.L] using hlog
  simpa [K, c] using
    divisorCompensation_product_bound x D z hx hL hD hDsmall hlarge

example : Erdos821.S56Core.DivisorCompensationTask :=
  @divisorCompensationTask_proof


end Erdos821.S9Div
