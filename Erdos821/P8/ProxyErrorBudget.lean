import Erdos821.P8.NonprincipalProxy

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

theorem eventually_nonprincipal_error_budget (b B S : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hS : 2 * B + 3 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ u : ℝ, |u| ≤ L x ^ B →
      4 * L x ^ (S + 1) * L x ^ B *
          (Real.exp 1 * L x ^ (-(S + 2 * B + 10)) + x ^ (-3 * b / 16)) +
        2 * (1 + |u|) * L x ^ (-S) * (1 + 2 * L x) ≤ L x ^ (-B) / 2 := by
  have ht1 : Tendsto (fun x : ℝ => 4 * Real.exp 1 * L x ^ (-9 : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, L, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9)).comp
      Real.tendsto_log_atTop).const_mul (4 * Real.exp 1)
  have ht2 : Tendsto (fun x : ℝ => 4 * (L x ^ (S + 1 + 2 * B) / x ^ (3 * b / 16)))
      atTop (nhds 0) := by
    simpa using (tendsto_log_rpow_div_rpow (S + 1 + 2 * B) (3 * b / 16) (by linarith)).const_mul 4
  have ht3 : Tendsto (fun x : ℝ => 12 * L x ^ (2 * B + 1 - S)) atTop (nhds 0) := by
    have hneg : 0 < -(2 * B + 1 - S) := by linarith
    simpa only [neg_neg, Function.comp_def, L, mul_zero] using
      ((tendsto_rpow_neg_atTop hneg).comp Real.tendsto_log_atTop).const_mul 12
  let R := fun x : ℝ => 4 * Real.exp 1 * L x ^ (-9 : ℝ) +
    4 * (L x ^ (S + 1 + 2 * B) / x ^ (3 * b / 16)) + 12 * L x ^ (2 * B + 1 - S)
  have hR : Tendsto R atTop (nhds 0) := by simpa only [add_zero] using (ht1.add ht2).add ht3
  have hsmall : ∀ᶠ x : ℝ in atTop, R x ≤ (1 / 2 : ℝ) :=
    (hR.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL, hsmall] with x hx hLx hRx
  intro u hu
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L x := zero_lt_one.trans_le hLx
  have hLB : 1 ≤ L x ^ B := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hLx hB.le
  have hvar : 2 * (1 + |u|) * L x ^ (-S) * (1 + 2 * L x) ≤
      12 * L x ^ (B + 1 - S) := by
    calc
      _ ≤ 2 * (2 * L x ^ B) * L x ^ (-S) * (3 * L x) := by gcongr <;> linarith
      _ = _ := by
        rw [show B + 1 - S = B + (-S) + 1 by ring, Real.rpow_add hL0,
          Real.rpow_one, Real.rpow_add hL0]
        ring
  have he1 : L x ^ (S + 1) * L x ^ B * L x ^ (-(S + 2 * B + 10)) =
      L x ^ (-B) * L x ^ (-9 : ℝ) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    ring
  have he2 : L x ^ (S + 1) * L x ^ B = L x ^ (-B) * L x ^ (S + 1 + 2 * B) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    ring
  have he3 : L x ^ (B + 1 - S) = L x ^ (-B) * L x ^ (2 * B + 1 - S) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hxneg : x ^ (-3 * b / 16) = (x ^ (3 * b / 16))⁻¹ := by
    rw [show -3 * b / 16 = -(3 * b / 16) by ring, Real.rpow_neg hx0.le]
  calc
    _ ≤ 4 * L x ^ (S + 1) * L x ^ B *
          (Real.exp 1 * L x ^ (-(S + 2 * B + 10)) + x ^ (-3 * b / 16)) +
        12 * L x ^ (B + 1 - S) := add_le_add le_rfl hvar
    _ = L x ^ (-B) * R x := by
      calc
        _ = 4 * Real.exp 1 * (L x ^ (S + 1) * L x ^ B * L x ^ (-(S + 2 * B + 10))) +
            4 * (L x ^ (S + 1) * L x ^ B) * x ^ (-3 * b / 16) +
            12 * L x ^ (B + 1 - S) := by ring
        _ = _ := by rw [he1, he2, he3, hxneg]; dsimp [R]; rw [div_eq_mul_inv]; ring
    _ ≤ L x ^ (-B) * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hRx (Real.rpow_nonneg hL0.le _)
    _ = L x ^ (-B) / 2 := by ring

theorem eventually_nonprincipal_proxy_bound (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b kappa B S : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hS : 2 * B + 3 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (a z r : ℕ)
      (chi : DirichletCharacter ℂ r) (u : ℝ),
      TestAllowed b kappa I → x ^ (b / 4) ≤ (a : ℝ) → a ≤ z →
      (z : ℝ) ≤ x ^ (1 - b / 4) → 1 ≤ r → (r : ℝ) ≤ L x ^ B → chi ≠ 1 → |u| ≤ L x ^ B →
      ‖∑ v ∈ Finset.Icc a z, (proxy I x S v : ℂ) * chi (v : ZMod r) *
        mellin v u / (v : ℂ)‖ ≤ L x ^ (-B) / 2 := by
  have hA : 0 < S + 2 * B + 10 := by linarith
  have hBS : B < S := by linarith
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_proxy_interval_estimate hc hs hresidue b kappa B S (S + 2 * B + 10) hb hB hA hBS,
    eventually_nonprincipal_error_budget b B S hb hB hS] with x hx hestimate hbudget
  intro I a z r chi u hallowed halo haz hzhi hr hrB hchi hu
  have hx0 : 0 < x := by linarith
  have ha : 0 < a := by exact_mod_cast (Real.rpow_pos_of_pos hx0 (b / 4)).trans_le halo
  have hzprobe : (z : ℝ) ≤ x ^ (2 : ℕ) := by
    apply hzhi.trans
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : 1 - b / 4 ≤ 2)
  have hm := interval_harmonic_mass_le_probe hx ha hzprobe
  have hM : 0 ≤ 2 * (1 + |u|) * L x ^ (-S) :=
    mul_nonneg (by positivity) (cell_width_pos hx S).le
  have h := hestimate I a z r chi u hallowed halo haz hzhi hr hrB hchi hu
  apply (h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm hM))).trans
  exact hbudget u hu

end Erdos821.P8Core

