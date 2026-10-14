import Erdos821.S56.GroupTail
import Erdos821.S56.RoughDivisorBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- A Rankin exponential with exponent above one half absorbs the rough
divisor loss exp(A sqrt L) and every fixed logarithmic power. -/
theorem exponential_tail_saving (r sigma A C D : ℝ)
    (hr : 1/2 < r) (hsigma : 0 < sigma) :
    ∀ᶠ t : ℝ in atTop,
      t^C * Real.exp (-sigma*t^r + A*Real.sqrt t) ≤ t^(-D) := by
  let a := |A|+1
  let c := |C+D|+1
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hr0 : 0 < r := by linarith
  have heps : 0 < sigma/(2*c) := by positivity
  have hlog := (isLittleO_log_rpow_atTop hr0).def heps
  have hpower := (tendsto_rpow_atTop (by linarith : 0 < r-1/2)).eventually_ge_atTop (2*a/sigma)
  filter_upwards [hlog, hpower, eventually_ge_atTop 1] with t hlog hpower ht
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have ht0 : 0 ≤ t := htpos.le
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hpow0 : 0 ≤ t^r := Real.rpow_nonneg ht0 _
  have hsqrt0 : 0 ≤ t^(1/2:ℝ) := Real.rpow_nonneg ht0 _
  have hC : C+D ≤ c := by dsimp [c]; linarith [le_abs_self (C+D)]
  have hA : A ≤ a := by dsimp [a]; linarith [le_abs_self A]
  have hlog' : Real.log t ≤ sigma/(2*c)*t^r := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hpow0] using hlog
  have hlogbound : (C+D)*Real.log t ≤ (sigma/2)*t^r := by
    have h := mul_le_mul_of_nonneg_left hlog' hc.le
    have hid : c*(sigma/(2*c)) = sigma/2 := by field_simp
    have h' := mul_le_mul_of_nonneg_right hC hlog0
    rw [← mul_assoc, hid] at h
    exact h'.trans h
  have hpowid : t^r = t^(1/2:ℝ)*t^(r-1/2) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  have hpower' : a ≤ (sigma/2)*t^(r-1/2) := by
    have h := (div_le_iff₀ hsigma).mp hpower
    nlinarith
  have hsqrtbound : A*Real.sqrt t ≤ (sigma/2)*t^r := by
    rw [Real.sqrt_eq_rpow, hpowid]
    exact (mul_le_mul_of_nonneg_right hA hsqrt0).trans
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hpower' hsqrt0)
  rw [Real.rpow_def_of_pos htpos C, Real.rpow_def_of_pos htpos (-D), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem group_exponential_tail_saving (P : Geometry) (sigma A C D : ℝ)
    (hsigma : 0 < sigma) :
    ∀ᶠ x : ℝ in atTop,
      L x^C * Real.exp (-sigma*L x^(1-P.d) + A*Real.sqrt (L x)) ≤ L x^(-D) := by
  have hd := P.ordered.2.2.2.2
  exact tendsto_L.eventually (exponential_tail_saving (1-P.d) sigma A C D (by linarith) hsigma)

/-- The ordinary discarded mass still saves any log power after paying the
rough-divisor factor, uniformly in the exceptional band and finite cutoff. -/
theorem discarded_mass_saving (hc : ClassicalInputs) (D : BandData) (hD : D.Valid)
    (sigma A C Dsave : ℝ) (hsigma : 0 < sigma) :
    ∀ᶠ x : ℝ in atTop, ∀ jstar N : ℕ,
      L x^C * Real.exp (A*Real.sqrt (L x)) *
        (∑ u ∈ Finset.Icc 1 N,
          if x^sigma < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0) ≤
        (N:ℝ)*L x^(-Dsave) := by
  obtain ⟨Ct, ht⟩ := ordinary_group_tail hc D hD sigma hsigma
  filter_upwards [ht, group_exponential_tail_saving D.geometry sigma A (C+Ct) Dsave hsigma,
    tendsto_L.eventually (eventually_gt_atTop 0)] with x ht hs hL
  intro jstar N
  have hraw := mul_le_mul_of_nonneg_left (ht jstar N)
    (by positivity : 0 ≤ L x^C * Real.exp (A*Real.sqrt (L x)))
  have hid : L x^C * Real.exp (A*Real.sqrt (L x)) *
      ((N:ℝ)*L x^Ct*Real.exp (-sigma*L x^(1-D.geometry.d))) =
      (N:ℝ)*(L x^(C+Ct)*Real.exp (-sigma*L x^(1-D.geometry.d)+A*Real.sqrt (L x))) := by
    rw [Real.rpow_add hL, Real.exp_add]
    ring
  rw [hid] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N))


end Erdos821.S56Core
