import Erdos821.P10.Extraction
import Erdos821.S10.Tasks

/-! Sharp presieve lower bound with the block-sieve witness fixed first. -/
noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S10Sharp
open Erdos821.Blueprint Erdos821.P10 Erdos821.P7Core
attribute [local instance] Classical.propDecidable

/-- The presieve lower bound with the uniform block-sieve witness supplied
explicitly, so its constants can be fixed before the presieve exponent. -/
theorem candidate_presieve_lower_of_witness
    (hc : ClassicalInputs) (hp : ProxyInputs) (C : CandidateData) (δ : ℝ)
    (hBounds : C.Bounds δ) (hTypeI : C.TypeI)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (Kdens Kblock : ℝ) (hKdens : 0 < Kdens) (hKblock : 0 < Kblock)
    (hInterval : ∀ w : ℝ, 1 < w →
      (∑ p ∈ ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))),
        1 / ((p : ℝ) - 1)) ≤ Kdens)
    (h₀ : ℕ) (hBlock : BlockSieveWitness Kdens Kblock h₀)
    (b θ εp εr : ℝ) (hb : 0 < b) (hθ : θ < 1 / 2)
    (hεp : 0 < εp) (hεr : 0 < εr) :
    ∀ h : ℕ, h₀ ≤ h → Even h → b * (4 * (h : ℝ) + 2) < θ →
      ∀ᶠ x : ℝ in atTop,
        ((if Kblock * Real.exp (-(h : ℝ)) ≤ 1 then
            (1 - Kblock * Real.exp (-(h : ℝ))) *
              (Real.exp (-Real.eulerMascheroniConstant) * singularSeries / b - εp)
          else
            (1 - Kblock * Real.exp (-(h : ℝ))) *
              (Real.exp (-Real.eulerMascheroniConstant) * singularSeries / b + εp)) - εr) *
            C.mass x jstar / Analytic.L x ≤ candidateSiftedMass C x jstar (x ^ b) := by
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩
  let D : ℝ := max 1 (CA + 20)
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hDtail : CA + 18 ≤ D := le_trans (by linarith) (le_max_right _ _)
  obtain ⟨Ktype, hKtype, hTypeIEvent⟩ :=
    hTypeI θ D hθ hDpos jstar hjstar
  have hBoundEvent := hBound jstar hjstar
  have hCutEvent (h : ℕ) (hExp : b * (4 * (h : ℝ) + 2) < θ) :
      ∀ᶠ x : ℝ in atTop, (x ^ b) ^ (4 * h + 2) ≤ x ^ θ :=
    eventually_sieve_level_below_typeI b θ h hExp
  have hYEvent : ∀ᶠ x : ℝ in atTop, 1 < x ^ b :=
    (tendsto_rpow_atTop hb).eventually (eventually_gt_atTop 1)
  have hXEvent : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  have hLogEvent : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.L x := by
    simpa [Analytic.L] using (Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  have hProductLower := eventually_shiftedSieveProduct_log_lower hc hp b εp hb hεp
  have hProductUpper := eventually_shiftedSieveProduct_log_upper hc hp b εp hb hεp
  have hTailTendsto : Tendsto
      (fun x : ℝ => 2 * Kblock * Ktype * (Analytic.L x) ^ (-17 : ℝ))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => 2 * Kblock * Ktype) atTop
        (nhds (2 * Kblock * Ktype)) := tendsto_const_nhds
    have hlogpow :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17)).comp Real.tendsto_log_atTop
    simpa [Analytic.L, mul_assoc] using hconst.mul hlogpow
  have hTailEvent : ∀ᶠ x : ℝ in atTop,
      2 * Kblock * Ktype * (Analytic.L x) ^ (-17 : ℝ) < εr :=
    hTailTendsto.eventually (Iio_mem_nhds hεr)
  intro h hh heven hExp
  have hCutoff := hCutEvent h hExp
  filter_upwards [hBoundEvent, hTypeIEvent, hCutoff, hYEvent, hXEvent, hLogEvent,
    hProductLower, hProductUpper, hTailEvent] with x hData hTypeRem hCut hyx hx hL
      hPlo hPhi hTail
  rcases hData with ⟨hMassLower, hHQLower, hHQUpper, hWeights, hWeightUpper, hSupport⟩
  have hx0 : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  have hLpos : 0 < Analytic.L x := lt_of_lt_of_le zero_lt_one hL
  have hLnonneg : 0 ≤ Analytic.L x := le_of_lt hLpos
  have hMass0 : 0 ≤ C.mass x jstar := by
    apply le_trans ?_ hMassLower
    exact mul_nonneg hx0 (Real.rpow_nonneg hLnonneg _)
  have hDens := candidateSieve_densityBounds_fromInterval C x jstar (x ^ b)
    Kdens hInterval hWeights hMass0 hyx
  let S := candidateSieveData C x jstar (x ^ b) hWeights hMass0
  have hApprox := (hBlock ℕ S (x ^ b) hDens).2 h hh heven |>.1
  have hlow := (abs_le.mp hApprox).1
  have hXeq : S.X = C.mass x jstar := rfl
  have hPeq : S.product = shiftedSieveProduct (x ^ b) :=
    candidateSieve_product C x jstar (x ^ b) hWeights hMass0
  have hSeq : S.sifted = candidateSiftedMass C x jstar (x ^ b) :=
    candidateSieve_sifted_eq C x jstar (x ^ b) hWeights hMass0
  have hBlockLower : candidateSiftedMass C x jstar (x ^ b) ≥
      C.mass x jstar * shiftedSieveProduct (x ^ b) -
        (Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar * shiftedSieveProduct (x ^ b) -
        Kblock * S.remainderSum ((x ^ b) ^ (4 * h + 2)) := by
    have hlow' := hlow
    rw [hSeq, hXeq, hPeq] at hlow'
    linarith [hlow']
  have hRemS := candidateSieve_remainderSum_le_typeI C x jstar (x ^ b)
    ((x ^ b) ^ (4 * h + 2)) θ hWeights hMass0 hCut
  have hRemType : S.remainderSum ((x ^ b) ^ (4 * h + 2)) ≤
      Ktype * (x * (Analytic.L x) ^ (-D) + C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ)) := by
    dsimp [S]
    exact le_trans hRemS hTypeRem
  have hMassTail := x_log_power_tail_le_mass_log18 x (Analytic.L x) CA D
    (C.mass x jstar) hx0 hL hDtail hMassLower
  have hSumTail : x * (Analytic.L x) ^ (-D) +
      C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ) ≤
        2 * C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ) := by
    linarith [hMassTail]
  have hTypeRem' := mul_le_mul_of_nonneg_left hSumTail hKtype.le
  have hRemBlock : Kblock * S.remainderSum ((x ^ b) ^ (4 * h + 2)) ≤
      εr * C.mass x jstar / Analytic.L x := by
    have hpowRel : (Analytic.L x) ^ (-18 : ℝ) * Analytic.L x =
        (Analytic.L x) ^ (-17 : ℝ) := by
      calc
        (Analytic.L x) ^ (-18 : ℝ) * Analytic.L x =
            (Analytic.L x) ^ (-18 : ℝ) * (Analytic.L x) ^ (1 : ℝ) := by simp
        _ = (Analytic.L x) ^ ((-18 : ℝ) + 1) :=
          (Real.rpow_add hLpos (-18 : ℝ) 1).symm
        _ = (Analytic.L x) ^ (-17 : ℝ) := by congr 1 <;> ring
    have hpowInv : (Analytic.L x) ^ (-18 : ℝ) =
        (Analytic.L x) ^ (-17 : ℝ) * (Analytic.L x)⁻¹ := by
      calc
        _ = ((Analytic.L x) ^ (-18 : ℝ) * Analytic.L x) * (Analytic.L x)⁻¹ := by
          field_simp [ne_of_gt hLpos]
        _ = (Analytic.L x) ^ (-17 : ℝ) * (Analytic.L x)⁻¹ := by rw [hpowRel]
    have hcoeffEq :
        2 * Kblock * Ktype * (Analytic.L x) ^ (-18 : ℝ) * C.mass x jstar =
          (2 * Kblock * Ktype * (Analytic.L x) ^ (-17 : ℝ)) *
            (C.mass x jstar / Analytic.L x) := by
      rw [hpowInv]
      field_simp [ne_of_gt hLpos]
    calc
      Kblock * S.remainderSum ((x ^ b) ^ (4 * h + 2)) ≤
          Kblock * (Ktype * (x * (Analytic.L x) ^ (-D) +
            C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ))) :=
        mul_le_mul_of_nonneg_left hRemType hKblock.le
      _ ≤ Kblock * (Ktype * (2 * C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ))) :=
        mul_le_mul_of_nonneg_left hTypeRem' hKblock.le
      _ = 2 * Kblock * Ktype * (Analytic.L x) ^ (-18 : ℝ) * C.mass x jstar := by ring
      _ = (2 * Kblock * Ktype * (Analytic.L x) ^ (-17 : ℝ)) *
            (C.mass x jstar / Analytic.L x) := hcoeffEq
      _ ≤ εr * (C.mass x jstar / Analytic.L x) :=
        mul_le_mul_of_nonneg_right hTail.le (div_nonneg hMass0 hLpos.le)
      _ = εr * C.mass x jstar / Analytic.L x := by ring
  exact sieve_lower_from_product_bounds (C.mass x jstar) (shiftedSieveProduct (x ^ b))
    (Analytic.L x) (Real.exp (-Real.eulerMascheroniConstant) * singularSeries)
    b εp (Kblock * Real.exp (-(h : ℝ)))
    (Kblock * S.remainderSum ((x ^ b) ^ (4 * h + 2))) εr
    (candidateSiftedMass C x jstar (x ^ b))
    hMass0 hLpos hPlo hPhi hBlockLower hRemBlock

end Erdos821.S10Sharp
