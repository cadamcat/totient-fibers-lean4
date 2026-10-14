import Erdos821.P7.Positivity
import Erdos821.P7.RoughCoefficient
import Erdos821.P6Sq.EndpointSquareTask
import Erdos821.S56.GroupParts

noncomputable section
open Filter
open scoped ContDiff

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem cutoff_bound (psi : ℝ → ℝ) (hc : Continuous psi)
    (hs : Function.support psi ⊆ Set.Icc 1 2) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ y, psi y ≤ B := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 1, le_max_right _ _, ?_⟩
  intro y
  by_cases hy : y ∈ Set.Icc (1 : ℝ) 2
  · have hb : |psi y| ≤ M := by simpa only [Real.norm_eq_abs] using hM y hy
    exact (le_abs_self (psi y)).trans (hb.trans (le_max_left _ _))
  · have hzero : psi y = 0 := by
      by_contra hne
      exact hy (hs hne)
    rw [hzero]
    exact zero_le_one.trans (le_max_right _ _)

theorem polylog_mul_exp_sqrt_bound (B A x : ℝ) (hB : 1 ≤ B) (hA : 0 ≤ A)
    (hL : 1 ≤ L x) :
    B * L x ^ A * Real.exp (2 * Real.sqrt (L x)) ≤
      Real.exp ((Real.log B + 2 * A + 2) * Real.sqrt (L x)) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hLp : 0 < L x := zero_lt_one.trans_le hL
  have hs : 1 ≤ Real.sqrt (L x) := by
    simpa using Real.sqrt_le_sqrt hL
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogL : Real.log (L x) ≤ 2 * Real.sqrt (L x) := by
    have h := Real.log_le_rpow_div hLp.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  conv_lhs => rw [← Real.exp_log hBp, Real.rpow_def_of_pos hLp, ← Real.exp_add,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlogL hA
  nlinarith

/-- Pointwise candidate control, uniform in every fixed rough-slot index.
Only the eventual threshold depends on that index. -/
theorem candidate_pointwise_bound (δ : ℝ) (C : CandidateData) (hC : C.Geometry δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop,
      ∀ u : ℕ, C.weighted x jstar u ≤ Real.exp (K * Real.sqrt (L x)) := by
  have hD : C.bands.Valid := hC.1
  rcases hC with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hcont, hsupp, hpsi0, _⟩
  obtain ⟨B, hB, hpsi⟩ := cutoff_bound C.psi hcont.continuous hsupp
  obtain ⟨A, hA, hmark⟩ := Erdos821.P6Sq.markWeight_log_bound C.bands.geometry
  let K := Real.log B + 2 * A + 2
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro jstar
  have hDcopy := hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, hdata⟩ := hDcopy
  filter_upwards [bandCoefficient_exp_bound C.bands hD jstar, hmark, hdata,
    eventually_ge_atTop (5 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hQ hP hg hx hL
  change 1 ≤ L x at hL
  intro u
  by_cases hu : C.weighted x jstar u = 0
  · rw [hu]
    exact (Real.exp_pos _).le
  · have hx0 : 0 < x := by linarith
    obtain ⟨hux, hxu⟩ := weighted_interval_support C hsupp x hx0 jstar u hu
    have hu0 : 0 < u := by exact_mod_cast hx0.trans_le hux
    have hv : 0 < groupFreePart (C.bands.groups x) u :=
      Erdos821.S56Core.groupFreePart_pos _ _
    have hvu : groupFreePart (C.bands.groups x) u ≤ u :=
      Nat.le_of_dvd hu0 (Erdos821.S56Core.groupFreePart_dvd _ _ hu0)
    have hvx : (groupFreePart (C.bands.groups x) u : ℝ) ≤ 5 * x := by
      have hvu' : (groupFreePart (C.bands.groups x) u : ℝ) ≤ u := by exact_mod_cast hvu
      linarith
    have hQ' := hQ _ hv hvx
    have hP' := hP (C.bands.groups x) hg.1 u
    have hmark0 := markWeight_nonneg (C.bands.groups x) C.bands.geometry.q
      C.bands.geometry.damping.1.le (fun _ => C.bands.geometry.ell) u
    have hweight0 : 0 ≤ C.bands.weight x jstar u :=
      mul_nonneg (bandCoefficient_nonneg _ _ _ _) hmark0
    have hweight : C.bands.weight x jstar u ≤
        Real.exp (2 * Real.sqrt (L x)) * L x ^ A :=
      mul_le_mul hQ' hP' hmark0 (Real.exp_pos _).le
    calc
      C.weighted x jstar u ≤ (Real.exp (2 * Real.sqrt (L x)) * L x ^ A) * B :=
        mul_le_mul hweight (hpsi _) (hpsi0 _)
          (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _))
      _ = B * L x ^ A * Real.exp (2 * Real.sqrt (L x)) := by ring
      _ ≤ Real.exp (K * Real.sqrt (L x)) :=
        polylog_mul_exp_sqrt_bound B A x hB hA.le hL

end Erdos821.P7Core

