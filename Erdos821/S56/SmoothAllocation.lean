import Erdos821.S56.GoodTuple
import Erdos821.S56.AllocatedFactors
import Erdos821.S56.SplittingScale

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem argumentRadius_pos (D : BandData) (hD : D.Valid) : 0 < argumentRadius D := by
  have hc2 : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
  have hr : 1 < D.ratio := hD.2.2.2.2.1
  have hden : 0 < 1 - D.ratio⁻¹ := by
    have hi : D.ratio⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hr)).mpr hr
    linarith
  unfold argumentRadius
  positivity

/-- The complete positive smooth allocation of a good literal slot tuple.
Cs is chosen from fixed band data before b, jstar, K₀ or any Fourier saving. -/
theorem smooth_allocation (D : BandData) (hD : D.Valid) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ b : ℝ, 0 < b → ∀ jstar : ℕ,
      D.c₂ * D.s' / D.ratio ^ jstar < b / 4 → ∀ K0 : ℝ, 0 ≤ K0 →
        ∀ᶠ x : ℝ in atTop, ∀ (U : ℝ) (u : ℕ) (z : D.Lists x jstar),
          x ^ b ≤ U → U ≤ x ^ (1 - b) → x ≤ (u : ℝ) →
          D.listProduct z = groupFreePart (D.groups x) u →
          (groupPart (D.groups x) u : ℝ) ≤ x ^ (b / 4) →
          (∑ delta : ProcessedIndex D x jstar → Bool,
            clippedBranchMass (pureIndices D x jstar).card (Real.log (U * L x ^ (-K0)))
              (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta) = 1 ∧
          ∀ delta : ProcessedIndex D x jstar → Bool,
            0 < clippedBranchMass (pureIndices D x jstar).card (Real.log (U * L x ^ (-K0)))
              (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta →
            (U * L x ^ (-K0)) * L x ^ (-Cs) ≤ (processedFactor D z delta : ℝ) ∧
              (processedFactor D z delta : ℝ) ≤ U * L x ^ (-K0) := by
  have hdata := hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, hcmin, hcmax, hevent⟩ := hdata
  have hc2 : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
  let Cs := (D.c₂ + 1) * cmax
  refine ⟨Cs, mul_pos (by linarith) hcmax, ?_⟩
  intro b hb jstar heta K0 hK0
  filter_upwards [hevent, eventually_exceptional_present D hD jstar,
    eventually_splitting_scale b K0 hb hK0, tendsto_L.eventually (eventually_ge_atTop 1),
    eventually_gt_atTop 1] with x hx hj hEsc hL1 hx1
  intro U u z hUlo hUhi hu hz hgood
  have hL : 0 < L x := zero_lt_one.trans_le hL1
  have hT : 0 ≤ T x := Real.log_nonneg hL1
  have hU : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) b).trans_le hUlo
  let E := U * L x ^ (-K0)
  have hE1 : 1 ≤ E := hEsc U hUlo
  have hE : 0 < E := zero_lt_one.trans_le hE1
  have ht : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hterm0 : 0 ≤ (D.c₂ + 1) * D.scale x (D.last x) :=
    mul_nonneg (by linarith) (scale_pos D hD x hL _).le
  have hinit0 := good_tuple_available D hD z hj u hz hx1 hu b U K0 hb hU hUhi hK0 hT heta hgood
  have hinit : Real.log E ≤ (∑ i, processedLog D z i) + (D.c₂ + 1) * D.scale x (D.last x) :=
    hinit0.trans (le_add_of_nonneg_right hterm0)
  refine ⟨literal_clipped_partition D hD z hL (Real.log E) ht hinit, ?_⟩
  intro delta hmass
  obtain ⟨hlo, hhi⟩ := literal_allocation_range D hD z hL (Real.log E) ht hinit delta hmass
  have htermb : (D.c₂ + 1) * D.scale x (D.last x) ≤ Cs * T x := by
    simpa only [Cs, mul_assoc] using
      mul_le_mul_of_nonneg_left hx.2.2.1 (by linarith : 0 ≤ D.c₂ + 1)
  have hbase : E * L x ^ (-Cs) = Real.exp (Real.log E - Cs * T x) := by
    symm
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hE, Real.rpow_def_of_pos hL]
    congr 1
    unfold T
    congr 1
    ring
  constructor
  · calc
      _ = Real.exp (Real.log E - Cs * T x) := hbase
      _ ≤ Real.exp (Real.log E - (D.c₂ + 1) * D.scale x (D.last x)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := hlo
  · simpa only [Real.exp_log hE] using hhi


end Erdos821.S56Core
