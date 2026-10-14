import Erdos821.P6Off.Range
import Erdos821.P6Off.Discrepancy

noncomputable section
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

def shiftCount (x K0 Cs : ℝ) : ℕ := ⌈L x ^ (K0 + Cs)⌉₊

/-- The logarithmic shift cutoff is large enough for all e in the smooth range. -/
theorem shiftCount_covers (x U K0 Cs : ℝ) (hL : 0 < L x) (hU : 0 < U) :
    U ≤ 2 * (U * L x ^ (-K0) * L x ^ (-Cs) / 2) * shiftCount x K0 Cs := by
  have hp : L x ^ (K0 + Cs) ≤ (shiftCount x K0 Cs : ℝ) := Nat.le_ceil _
  have hnegpos : 0 ≤ U * L x ^ (-K0) * L x ^ (-Cs) := by positivity
  calc
    U = (U * L x ^ (-K0) * L x ^ (-Cs)) * L x ^ (K0 + Cs) := by
      rw [Real.rpow_add hL, Real.rpow_neg hL.le K0, Real.rpow_neg hL.le Cs]
      field_simp [(Real.rpow_pos_of_pos hL K0).ne', (Real.rpow_pos_of_pos hL Cs).ne']
    _ ≤ (U * L x ^ (-K0) * L x ^ (-Cs)) * shiftCount x K0 Cs :=
      mul_le_mul_of_nonneg_left hp hnegpos
    _ = _ := by ring

/-- Both the shift count and its character modulus lie below W eventually. -/
theorem eventually_shiftCount_bounds (K0 Cs : ℝ) (hK : 0 < K0) (hCs : 0 < Cs) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ shiftCount x K0 Cs ∧
      (2 * shiftCount x K0 Cs : ℝ) ≤ L x ^ (K0 + Cs + 2) ∧
      (2 * shiftCount x K0 Cs : ℝ) ≤ W x := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hL.eventually (eventually_ge_atTop 2),
    eventually_log_rpow_le_W (K0 + Cs + 2)] with x hx hW
  have hLpos : 0 < L x := by linarith
  have hpowpos : 0 < L x ^ (K0 + Cs) := Real.rpow_pos_of_pos hLpos _
  have hpow1 : 1 ≤ L x ^ (K0 + Cs) := Real.one_le_rpow (by linarith) (by linarith)
  have hceil : (shiftCount x K0 Cs : ℝ) ≤ L x ^ (K0 + Cs) + 1 :=
    (Nat.ceil_lt_add_one hpowpos.le).le
  have hmul : (2 * shiftCount x K0 Cs : ℝ) ≤ L x ^ (K0 + Cs + 2) := by
    rw [Real.rpow_add hLpos (K0 + Cs) 2, Real.rpow_two]
    have hsq : (4 : ℝ) ≤ L x ^ (2 : ℕ) := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hsq hpowpos.le
    nlinarith
  refine ⟨?_, hmul, hmul.trans hW⟩
  exact Nat.one_le_ceil_iff.mpr hpowpos

theorem rough_unit_small_modulus (y : ℝ) (n r : ℕ)
    (hn : rough y n) (hr : 0 < r) (hsmall : (r : ℝ) ≤ y) : IsUnit (n : ZMod r) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpn hpr
  have hle : (p : ℝ) ≤ r := by exact_mod_cast Nat.le_of_dvd hr hpr
  exact (not_lt_of_ge (hle.trans hsmall)) (hn.2 p hp hpn)


end Erdos821.P6Off
