import Erdos821.P6Off.Precision

noncomputable section
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

theorem shift_natAbs_le (M : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (-(M : ℤ)) M) : k.natAbs ≤ M := by
  have habs : |k| ≤ (M : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hk)
  rw [← Int.natCast_natAbs] at habs
  exact_mod_cast habs

theorem shift_real_abs_le (M : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (-(M : ℤ)) M) :
    |(k : ℝ)| ≤ (M : ℝ) := by
  have habs : |k| ≤ (M : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hk)
  exact_mod_cast habs

theorem shift_interval_card (M : ℕ) :
    (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
  rw [Int.card_Icc]
  omega

theorem eventually_shift_interval_card_bound (K0 Cs : ℝ) (hK : 0 < K0) (hCs : 0 < Cs) :
    ∀ᶠ x : ℝ in atTop,
      ((Finset.Icc (-(shiftCount x K0 Cs : ℤ)) (shiftCount x K0 Cs)).card : ℝ) ≤
        L x ^ (K0 + Cs + 3) := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_shiftCount_bounds K0 Cs hK hCs,
    hL.eventually (eventually_ge_atTop 2)] with x hM hx
  rw [shift_interval_card]
  push_cast
  have hLpos : 0 < L x := by linarith
  have hpow1 : 1 ≤ L x ^ (K0 + Cs + 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hpow : L x ^ (K0 + Cs + 2) * 2 ≤ L x ^ (K0 + Cs + 3) := by
    rw [show K0 + Cs + 3 = (K0 + Cs + 2) + 1 by ring,
      Real.rpow_add hLpos (K0 + Cs + 2) 1, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hLpos.le _)
  nlinarith [hM.2.1]


end Erdos821.P6Off
