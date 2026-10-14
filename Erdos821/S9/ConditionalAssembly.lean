import Erdos821.S9.BudgetSummation
import Erdos821.S9.GeometryBounds
import Erdos821.S9.NormalizationTask
import Erdos821.P7.HarmonicPLower

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core

theorem balanced_rough_bound_of_tasks
    (hdiv : DivisorCompensationTask) (hmask : MaskHarmonicPTask)
    (hbudget : PairSieveBudgetTask) (hbridge : AssignmentSiftedBridgeTask)
    (hnormalize : BalancedNormalizationTask)
    (hc : ClassicalInputs) (hs : SieveInputs) (δ : ℝ) (C : CandidateData)
    (hC : C.Geometry δ) (hb : C.Bounds δ) : BalancedRoughBound C := by
  obtain ⟨A, K, hK, hBudget⟩ := hbudget hc hs hdiv hmask δ C hC
  obtain ⟨B, hB, hBridge⟩ := hbridge δ C hC hb
  let CQ : ℝ := ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) *
    (12 : ℝ) ^ (C.micro * C.bands.r₀)
  have hCQ : 0 < CQ := by dsimp [CQ]; positivity
  let Kpre : ℝ := B * (20 * K) * CQ
  have hKpre : 0 < Kpre := by dsimp [Kpre]; positivity
  obtain ⟨Kfinal, hKfinal, hNormalize⟩ := hnormalize hc δ C hC hb A Kpre hKpre
  refine ⟨Kfinal, hKfinal, ?_⟩
  intro jstar hj
  have hmicro : C.micro ≤ jstar := by
    have hmicro0 : C.micro ≤ C.j₀ := by
      rcases hC with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
      exact hm
    exact hmicro0.trans hj
  obtain ⟨Kc, CA, cmin, cmax, _, _, _, hBounds⟩ := hb
  filter_upwards [hBudget, geometry_assignment_bounds_eventually C δ hC,
    Erdos821.P7Core.geometry_harmonicP_ge_one C δ hC, hBounds jstar hj,
    hBridge jstar hj, microHarmonicMass_le_harmonicQ_eventually hc C δ hC jstar hmicro,
    hNormalize jstar hj, eventually_ge_atTop (1 : ℝ)]
    with x hBudgetX hAssign hHP hBoundsX hBridgeX hQ hNormalizeX hx
  intro M N hMlo hMhi hNlo hNhi
  have hM : 1 ≤ M := (Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 0.46)).trans hMlo
  have hN : 1 ≤ N := (Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 0.46)).trans hNlo
  by_cases hMN : M * N ≤ 5 * x
  · have hBudgetAssignments (m : MicroAssignments C x jstar)
        (marks : GlobalMarkChoices (C.bands.groups x))
        (hp : assignmentPrimeLower C x jstar m marks) :
        assignmentSiftedAverage C x M N jstar m marks ≤
          K * (((((⌈2 * M⌉₊ - ⌈M⌉₊ : ℕ) : ℝ) *
                ((⌈2 * N⌉₊ - ⌈N⌉₊ : ℕ) : ℝ)) /
                (assignmentModulus C x jstar m marks : ℝ)) *
              sieveProduct (W x) ^ 2 * sieveProduct (x ^ C.theta) * C.bands.harmonicP x +
            ((assignmentModulus C x jstar m marks : ℝ) * x ^ (0.1 : ℝ) +
              x ^ (0.59 : ℝ)) * L x ^ A) := by
      exact hBudgetX M N (assignmentModulus C x jstar m marks)
        (assignmentMaskPrimes C x marks) (assignmentModulus_pos C x jstar m marks)
        (by linarith) (by linarith) hMhi hNhi (hAssign.2 jstar m marks)
        hp Finset.sdiff_subset
    have hSum := assignmentSiftedSum_le_budget C x M N A K jstar hx hM hN hMN
      hK.le (zero_le_one.trans hHP) hAssign.1 (hAssign.2 jstar) hBudgetAssignments
    let V : ℝ := sieveProduct (W x) ^ 2 * sieveProduct (x ^ C.theta) * C.bands.harmonicP x
    have hfactor : 0 ≤ 20 * K * (x * V + x ^ (0.64 : ℝ) * L x ^ A) := by
      have hL : 0 ≤ L x := Real.log_nonneg hx
      have hV : 0 ≤ V := mul_nonneg
        (mul_nonneg (sq_nonneg _) (sieveProduct_pos _).le) (zero_le_one.trans hHP)
      positivity
    calc
      balancedRoughSum C x M N jstar ≤ B * assignmentSiftedSum C x M N jstar :=
        hBridgeX M N
      _ ≤ B * (20 * K * (x * V + x ^ (0.64 : ℝ) * L x ^ A) *
          microHarmonicMass C x jstar) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        simpa only [V, mul_assoc] using hSum
      _ ≤ B * (20 * K * (x * V + x ^ (0.64 : ℝ) * L x ^ A) *
          (CQ * C.bands.harmonicQ x jstar)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ hfactor) hB.le
      _ = Kpre *
          (x * sieveProduct (W x) ^ 2 * sieveProduct (x ^ C.theta) *
              C.bands.harmonicQ x jstar * C.bands.harmonicP x +
            x ^ (0.64 : ℝ) * L x ^ A * C.bands.harmonicQ x jstar) := by
        dsimp [Kpre, V]
        ring
      _ ≤ Kfinal * C.mass x jstar * sieveProduct (W x) ^ 2 := hNormalizeX
  · have hzero := balancedRoughSum_eq_zero_of_large_box C x M N jstar hx
      (by linarith) (by linarith) (lt_of_not_ge hMN)
      (fun u hu => (hBoundsX.2.2.2.2.2 u hu).2.1)
    rw [hzero]
    have hmass0 : 0 ≤ C.mass x jstar :=
      (mul_nonneg (zero_le_one.trans hx)
        (Real.rpow_nonneg (Real.log_nonneg hx) (-CA))).trans hBoundsX.1
    positivity

end Erdos821.S56Core

