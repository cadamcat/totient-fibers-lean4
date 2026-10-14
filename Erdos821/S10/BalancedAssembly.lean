import Erdos821.S10.BalancedTasks

noncomputable section
open Filter
namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.P10

/-- Cancel the rough-pair normalization before taking the shrinking-window tail. -/
theorem balanced_window_normalization (Kr Kp κ ε mass L V : ℝ)
    (hL : 0 < L) (hV : 0 < V) :
    Kp / (L ^ 2 * V ^ 2) * (Kr * (κ * L + 1) * mass * V ^ 2) +
        (ε / 2) * mass / L =
      (Kr * Kp * κ + Kr * Kp / L + ε / 2) * mass / L := by
  field_simp [hL.ne', hV.ne']
  <;> ring


/-- The uniform dyadic and proxy constants may be multiplied before choosing κ. -/
theorem balanced_composite_of_window_tasks
    (hFactor : BalancedFactorCoverageTask) (hRough : BalancedWindowRoughTask)
    (hPrime : BalancedWindowPrimeTask) : BalancedCompositeTask := by
  intro hc hII hp δ C hGeometry hBounds hBal
  obtain ⟨Kr, hKr, hRoughBound⟩ := hRough hc δ C hGeometry hBounds hBal
  obtain ⟨Kp, hKp, hPrimeBound⟩ := hPrime hc hII hp δ C hGeometry hBounds
  refine ⟨Kr * Kp, mul_pos hKr hKp, ?_⟩
  intro κ bstar hκ hκsmall hbstar hbstarSmall jstar hjstar hslot ε hε
  have hFactorEvent := hFactor δ C hBounds κ hκ hκsmall jstar hjstar
  have hRoughEvent := hRoughBound κ hκ hκsmall jstar hjstar
  have hPrimeEvent := hPrimeBound κ bstar hκ hκsmall hbstar hbstarSmall
    jstar hjstar hslot (ε / 2) (by positivity)
  have hTail : Tendsto (fun x : ℝ => Kr * Kp / Analytic.L x) atTop (nhds 0) := by
    simpa [Analytic.L] using tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hTailEvent : ∀ᶠ x : ℝ in atTop, Kr * Kp / Analytic.L x < ε / 2 :=
    hTail.eventually (Iio_mem_nhds (by positivity))
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBoundsEvent⟩
  filter_upwards [hFactorEvent, hRoughEvent, hPrimeEvent, hTailEvent,
    hBoundsEvent jstar hjstar, eventually_gt_atTop (1 : ℝ)]
    with x hF hR hP hT hData hx
  have hL : 0 < Analytic.L x := Real.log_pos hx
  have hV : 0 < sieveProduct (Analytic.W x) := sieveProduct_pos _
  have hMass : 0 ≤ C.mass x jstar :=
    le_trans (mul_nonneg (by linarith) (Real.rpow_nonneg hL.le _)) hData.1
  have hCoefficient : 0 ≤ Kp / (Analytic.L x ^ 2 * sieveProduct (Analytic.W x) ^ 2) :=
    le_of_lt (by positivity)
  calc
    balancedCompositeMass C x jstar κ ≤ balancedPrimeWindowMass C x jstar κ := hF
    _ ≤ Kp / (Analytic.L x ^ 2 * sieveProduct (Analytic.W x) ^ 2) *
        balancedRoughWindowMass C x jstar κ + (ε / 2) * C.mass x jstar / Analytic.L x := hP
    _ ≤ Kp / (Analytic.L x ^ 2 * sieveProduct (Analytic.W x) ^ 2) *
        (Kr * (κ * Analytic.L x + 1) * C.mass x jstar * sieveProduct (Analytic.W x) ^ 2) +
          (ε / 2) * C.mass x jstar / Analytic.L x :=
      add_le_add (mul_le_mul_of_nonneg_left hR hCoefficient)
        (le_refl ((ε / 2) * C.mass x jstar / Analytic.L x))
    _ = (Kr * Kp * κ + Kr * Kp / Analytic.L x + ε / 2) *
        C.mass x jstar / Analytic.L x := balanced_window_normalization _ _ _ _ _ _ _ hL hV
    _ ≤ (Kr * Kp * κ + ε) * C.mass x jstar / Analytic.L x := by
      apply div_le_div_of_nonneg_right _ hL.le
      apply mul_le_mul_of_nonneg_right _ hMass
      linarith


end Erdos821.P7Core
