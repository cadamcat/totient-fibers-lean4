import Erdos821.S56.GroupTailFinite
import Erdos821.S56.HarmonicQBound
import Erdos821.P6Mass.Mass

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem tilted_group_mass : TiltedGroupMassTask :=
  Erdos821.P6Mass.TiltedGroupMassTask_proof

example : TiltedGroupMassTask = Erdos821.P6Mass.TiltedGroupMassTask := rfl

/-- The paper's discarded group part has exponentially small ordinary mass.
The log power is independent of splitting precision and of the rough band. -/
theorem ordinary_group_tail (hc : ClassicalInputs) (D : BandData) (hD : D.Valid)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ, ∀ N : ℕ,
      (∑ u ∈ Finset.Icc 1 N,
        if x ^ sigma < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0) ≤
        (N : ℝ) * L x ^ C * Real.exp (-sigma * L x ^ (1 - D.geometry.d)) := by
  obtain ⟨CQ, hCQ, hQ⟩ := harmonicQ_polylog hc D hD
  obtain ⟨CP, hP⟩ := group_tail_of_tilted tilted_group_mass D.geometry sigma hsigma
  have hdata := hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, hcmin, hcmax, hvalid⟩ := hdata
  refine ⟨CQ + CP, ?_⟩
  filter_upwards [hQ, hP, hvalid, tendsto_L.eventually (eventually_gt_atTop 0)] with x hQ hP hx hL
  intro jstar N
  have htail := hP (D.groups x) hx.1 N
  have hraw := band_group_tail_bound D x jstar N (x ^ sigma)
  have htail0 : 0 ≤ ∑ r ∈ Finset.Icc 1 N,
      if groupFreePart (D.groups x) r = 1 ∧ x ^ sigma < (r : ℝ) then
        markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) r / r else 0 := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact div_nonneg (markWeight_nonneg _ _ D.geometry.damping.1.le _ _) (Nat.cast_nonneg r)
    · exact le_rfl
  have hmul := mul_le_mul
    (mul_le_mul_of_nonneg_left (hQ jstar) (Nat.cast_nonneg N)) htail htail0
    (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hL.le _))
  calc
    _ ≤ _ := hraw
    _ ≤ (N : ℝ) * L x ^ CQ *
        (Real.exp (-sigma * L x ^ (1 - D.geometry.d)) * L x ^ CP) := hmul
    _ = _ := by rw [Real.rpow_add hL]; ring


end Erdos821.S56Core
