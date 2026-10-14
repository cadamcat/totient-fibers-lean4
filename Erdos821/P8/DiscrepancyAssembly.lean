import Erdos821.P8.ProxyErrorBudget
import Erdos821.P8.NonprincipalTasks

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma proxy_difference_probe_sum_eq (I : FactorTest) (x S lo hi probeLo probeHi u : ℝ)
    {r : ℕ} (chi : DirichletCharacter ℂ r) (hhi : 0 ≤ hi) :
    (∑ n ∈ Finset.Icc ⌈probeLo⌉₊ ⌊probeHi⌋₊,
      proxyDifference I x S lo hi n * chi (n : ZMod r) * mellin n u / (n : ℂ)) =
    ∑ n ∈ Finset.Icc (max ⌈probeLo⌉₊ ⌈lo⌉₊) (min ⌊probeHi⌋₊ ⌊hi⌋₊),
      ((test I x n - proxy I x S n : ℝ) : ℂ) * chi (n : ZMod r) * mellin n u / (n : ℂ) := by
  calc
    _ = ∑ n ∈ Finset.Icc ⌈probeLo⌉₊ ⌊probeHi⌋₊,
        if lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi then
          ((test I x n - proxy I x S n : ℝ) : ℂ) * chi (n : ZMod r) * mellin n u / (n : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [proxyDifference]
      split_ifs <;> simp
    _ = _ := interval_restrict_sum _ _ lo hi hhi _

lemma stronger_log_saving_le_half {x : ℝ} (hL : 2 ≤ L x) (B : ℝ) :
    L x ^ (-(B + 1)) ≤ L x ^ (-B) / 2 := by
  have hL0 : 0 < L x := by linarith
  have hfactor : L x ^ (-(B + 1)) = L x ^ (-B) * (L x)⁻¹ := by
    rw [show -(B + 1) = -B + (-1 : ℝ) by ring, Real.rpow_add hL0, Real.rpow_neg_one]
  have hinv : (L x)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hL
  rw [hfactor]
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hL0.le (-B))

theorem proxyDiscrepancy_from_tasks (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (hactual : ActualTestNonprincipalTask) :
    ProxyDiscrepancy := by
  intro b kappa B hb hk hk50 hB S hS
  have hSpos : 0 < S := by linarith
  have hA : 0 < B + 1 := by linarith
  have hL : ∀ᶠ x : ℝ in atTop, 2 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL,
    eventually_proxy_bounds_from_residue hc hs hresidue b kappa S hb hSpos,
    eventually_principal_discrepancy_from_residue hc hs hresidue b kappa B S hb hB hS,
    eventually_nonprincipal_proxy_bound hc hs hresidue b kappa B S hb hB hS,
    hactual hc b kappa B (B + 1) hb hk hk50 hB hA]
    with x hx hLx hbounds hprincipal hproxy htest
  intro I lo hi hallowed hlo horder hhi
  constructor
  · intro probeLo probeHi u r chi hpLo hpOrder hpHi hr hrB hu
    by_cases hchi : chi = 1
    · rw [hchi]
      exact hprincipal I lo hi hallowed hlo horder hhi probeLo probeHi u r
        hpLo hpOrder hpHi hr hrB hu
    have hx0 : 0 < x := by linarith
    have hxpow : 0 < x ^ (b / 4) := Real.rpow_pos_of_pos hx0 _
    have hlo0 : 0 < lo := hxpow.trans_le hlo
    have hhi0 : 0 ≤ hi := (hlo0.trans_le horder).le
    rw [proxy_difference_probe_sum_eq I x S lo hi probeLo probeHi u chi hhi0]
    let a := max ⌈probeLo⌉₊ ⌈lo⌉₊
    let z := min ⌊probeHi⌋₊ ⌊hi⌋₊
    change ‖∑ n ∈ Finset.Icc a z, ((test I x n - proxy I x S n : ℝ) : ℂ) *
      chi (n : ZMod r) * mellin n u / (n : ℂ)‖ ≤ L x ^ (-B)
    by_cases haz : a ≤ z
    · have halo : x ^ (b / 4) ≤ (a : ℝ) :=
        hlo.trans ((Nat.le_ceil lo).trans (by exact_mod_cast (le_max_right ⌈probeLo⌉₊ ⌈lo⌉₊)))
      have hzhi : (z : ℝ) ≤ x ^ (1 - b / 4) :=
        ((Nat.le_floor_iff hhi0).mp (min_le_right ⌊probeHi⌋₊ ⌊hi⌋₊)).trans hhi
      have haz' : (a : ℝ) ≤ z := by exact_mod_cast haz
      have hzprobe : (z : ℝ) ≤ x ^ (2 : ℕ) := by
        apply hzhi.trans
        simpa only [Real.rpow_two] using
          Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : 1 - b / 4 ≤ 2)
      have hactual' := htest I (a : ℝ) (z : ℝ) u r chi hallowed halo haz' hzprobe hr hrB hchi hu
      simp only [Nat.ceil_natCast, Nat.floor_natCast] at hactual'
      have hactualHalf := hactual'.trans (stronger_log_saving_le_half hLx B)
      have hproxyHalf := hproxy I a z r chi u hallowed halo haz hzhi hr hrB hchi hu
      have heq : (∑ n ∈ Finset.Icc a z, ((test I x n - proxy I x S n : ℝ) : ℂ) *
          chi (n : ZMod r) * mellin n u / (n : ℂ)) =
          (∑ n ∈ Finset.Icc a z, (test I x n : ℂ) * chi (n : ZMod r) * mellin n u / (n : ℂ)) -
          (∑ n ∈ Finset.Icc a z, (proxy I x S n : ℂ) * chi (n : ZMod r) * mellin n u / (n : ℂ)) := by
        simp only [Complex.ofReal_sub, sub_mul, sub_div, Finset.sum_sub_distrib]
      rw [heq]
      exact (norm_sub_le _ _).trans (by linarith)
    · rw [Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge haz), Finset.sum_empty, norm_zero]
      exact Real.rpow_nonneg (Real.log_pos hx).le _
  · intro n hnlo hnhi
    have h := hbounds I n hallowed (hlo.trans hnlo) (hnhi.trans hhi)
    exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

end Erdos821.P8Core

