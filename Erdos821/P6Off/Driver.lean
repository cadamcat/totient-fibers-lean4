import Erdos821.P6Off.DyadPowerBound
import Erdos821.P6Off.EndpointBounds
import Erdos821.P6Off.FrequencyBound
import Erdos821.P6Off.Truncation
import Erdos821.P6Off.ShiftCard
import Erdos821.P6Off.SumPowers
import Erdos821.P6Off.DyadicNorm

noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- Assembly of the exact arithmetic reduction, quantitative cutoff separation
and absolute endpoint control. Every precision is chosen before discrepancy B. -/
theorem offDiagonalShiftTask_of_tasks
    (hreindex : OffDiagonalReindexTask) (hseparation : PulledCutoffSeparationTask)
    (habsolute : AbsoluteDeterminantDyadTask) (hsquares : EndpointSquareTask) :
    OffDiagonalShiftTask := by
  intro hc hshift P A b C Cs K0 tau eta bounds hA hb hC hCs hK0 htau htaueta heta hetab hbounds
  let Cz := K0 + Cs + 1
  let CZ := Cz + 2
  have hCz : 0 < Cz := by dsimp [Cz]; linarith
  have hCZ : 0 < CZ := by dsimp [CZ]; linarith
  obtain ⟨localBounds, hlocalBounds, hlocalDeriv⟩ := logLocalizer_derivative_bounds
  obtain ⟨Cf, Kf, hCf, hKf, hsep⟩ := hseparation hc C K0 CZ 2 bounds localBounds logLocalizer
    hC hK0 hCZ (by norm_num) (fun j => ⟨hbounds j, hlocalBounds j⟩)
    logLocalizer_contDiff logLocalizer_support hlocalDeriv
  obtain ⟨Ct, Ktail, hCt, hKtail, habs⟩ := habsolute hc hsquares P C hC
  let Ce := max (max C Cf + 1) CZ
  have hCeFreq : max C Cf + 1 ≤ Ce := le_max_left _ _
  have hCeCZ : CZ ≤ Ce := le_max_right _ _
  have hCe : 0 < Ce := hCZ.trans_le hCeCZ
  let D := A + Kf + 2 * Ce + 2
  let At := A + Ct + 2 * Ce + 2
  have hD : 0 < D := by dsimp [D]; linarith
  have hAt : 0 < At := by dsimp [At]; linarith
  obtain ⟨Kat, hKat, hsepX⟩ := hsep At hAt
  obtain ⟨B, Kmain, hB, hKmain, hfreqX⟩ := frequencyDyad_bound hshift P D Ce tau eta hD hCe
  let Ktotal := Kmain + Kat * Ktail
  have hKtotal : 0 < Ktotal := add_pos hKmain (mul_pos hKat hKtail)
  refine ⟨B, Ktotal, hB, hKtotal, ?_⟩
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hsepX, habs, hfreqX, eventually_shiftEndpoint_frequency_bounds C Cf CZ,
    eventually_dyadic_scales Cz hCz, eventually_determinantSum_dyadic_partition K0 Cs hK0 hCs,
    eventually_shiftCount_bounds K0 Cs hK0 hCs, eventually_shift_interval_card_bound K0 Cs hK0 hCs,
    eventually_log_rpow_le_x_rpow (2 * Ce + 2) 1 (by norm_num),
    eventually_log_rpow_le_x_rpow (Ce + 1) b hb,
    eventually_ge_atTop (32 : ℝ), hL.eventually (eventually_ge_atTop 128)]
    with x hsep habs hfreq hframe hdyads hpartition hshifts hcard hgrowth hgrowthb hx32 hxL
  intro G U V lo hi rho sigma c alpha etae etan hG hUVlo hUVhi hUb hUhi hVb hVhi
    hlo hlohi hhi hrho hsigma hcoef hrough hdisc hce hcn hse hsn hderiv
  have hxpos : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLpos : 0 < L x := by linarith
  have hL1 : 1 ≤ L x := by linarith
  have hL2 : 2 ≤ L x := by linarith
  have hL3 : 3 ≤ L x := by linarith
  have hpowb : 1 ≤ x ^ b := Real.one_le_rpow hx1 hb.le
  have hU1 : 1 ≤ U := hpowb.trans hUb
  have hV1 : 1 ≤ V := hpowb.trans hVb
  have hUpos : 0 < U := zero_lt_one.trans_le hU1
  have hVpos : 0 < V := zero_lt_one.trans_le hV1
  have hgrowth' : L x ^ (2 * Ce + 2) ≤ x := by simpa only [Real.rpow_one] using hgrowth
  let E := U * L x ^ (-K0)
  let emin := E * L x ^ (-Cs) / 2
  let M := shiftCount x K0 Cs
  let N := determinantTruncation U V
  have hEpos : 0 < E := mul_pos hUpos (Real.rpow_pos_of_pos hLpos _)
  have heminpos : 0 < emin := by dsimp [emin]; positivity
  have hemin : emin / E = L x ^ (-Cs) / 2 := by dsimp [emin]; field_simp
  have hcover : U ≤ 2 * emin * M := shiftCount_covers x U K0 Cs hLpos hUpos
  have hse' : Function.support etae ⊆ Set.Icc (emin / E) 2 := by rw [hemin]; exact hse
  have hroughfree : ∀ m, alpha m ≠ 0 → GroupFree G m :=
    fun m hm => rough_groupFree P x G hL1 hG m (hrough m hm)
  have hreidx := hreindex M E U V emin (W x) etae etan
    (hCoefficient P G x lo hi rho sigma c) alpha hEpos hU1 hV1 heminpos hcover
    hshifts.2.2 hrough hse' hsn
  change ‖offDiagonalSum E U V etae etan (hCoefficient P G x lo hi rho sigma c) alpha‖ ≤ _
  rw [hreidx]
  change ‖determinantSum M N E U V etae etan (hCoefficient P G x lo hi rho sigma c) alpha‖ ≤ _
  rw [hpartition U V etae etan (hCoefficient P G x lo hi rho sigma c) alpha M N
    hUpos hVpos hUVlo hUVhi hse hsn]
  change ‖∑ j ∈ Finset.range (dyadicCount x Cz), ∑ k ∈ Finset.Icc (-(M : ℤ)) M,
    determinantAtShift P G x E U V (dyadicScale x Cz j) lo hi rho sigma N k etae etan c alpha‖ ≤ _
  apply sum_dyads_shifts_bound x (L x) A Ce Ktotal hxpos.le hLpos hKtotal.le
    (Finset.range (dyadicCount x Cz)) (Finset.Icc (-(M : ℤ)) M) (dyadicScale x Cz)
  · simpa only [Finset.card_range] using hdyads.2.1
  · apply hcard.trans
    apply Real.rpow_le_rpow_of_exponent_le hL1
    dsimp [CZ, Cz] at hCeCZ
    linarith
  · intro j hj
    exact (hdyads.2.2.1 j hj).2.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hCeCZ) hxpos.le)
  · intro j hj k hkM
    let Z := dyadicScale x Cz j
    obtain ⟨hZlo0, hZhi0⟩ := hdyads.2.2.1 j hj
    have hZlo : x * L x ^ (-Ce) ≤ Z :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg hCeCZ)) hxpos.le).trans hZlo0
    have hZhi : Z ≤ x * L x ^ Ce := hZhi0.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hCeCZ) hxpos.le)
    obtain ⟨hZ1, hZshift, hZsquare⟩ := log_window_aux x Ce Z hxpos hL3 hCe hgrowth' hZlo hZhi
    have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
    by_cases hk0 : k = 0
    · simp [determinantAtShift, determinantTerm, hk0] <;> positivity
    · have hk : k ≠ 0 := hk0
      let r := 2 * k.natAbs
      have hr : 0 < r := Nat.mul_pos (by norm_num) (Int.natAbs_pos.mpr hk)
      have hkabs : k.natAbs ≤ M := shift_natAbs_le M k hkM
      have hrM : (r : ℝ) ≤ (2 * M : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 2 hkabs
      have hrCZ : (r : ℝ) ≤ L x ^ CZ := hrM.trans (hshifts.2.1.trans
        (Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [CZ, Cz]; linarith)))
      have hrW : (r : ℝ) ≤ W x := hrM.trans hshifts.2.2
      have hkCe : |(k : ℝ)| ≤ L x ^ Ce := by
        calc
          _ ≤ (M : ℝ) := shift_real_abs_le M k hkM
          _ ≤ (2 * M : ℝ) := by linarith [show (0 : ℝ) ≤ M by positivity]
          _ ≤ L x ^ CZ := hshifts.2.1.trans
            (Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [CZ, Cz]; linarith))
          _ ≤ L x ^ Ce := Real.rpow_le_rpow_of_exponent_le hL1 hCeCZ
      have hunit : ∀ m, alpha m ≠ 0 → IsUnit (m : ZMod r) :=
        fun m hm => rough_unit_small_modulus (W x) m r (hrough m hm) hr hrW
      have hNcover : 2 * Z ≤ (N : ℝ) :=
        log_window_truncation x U V Ce b Z hxpos hL2 hU1 hV1 hUVlo hgrowthb hUb hZhi
      obtain ⟨a, ha, hL1a, hFa, htail⟩ := hsep U V Z k etae etan hU1 hV1 hUVlo hUVhi
        hZpos hZhi0 hk hce hcn hderiv
      have hmain : ∀ xi : Fin 3 → ℝ, ‖xi‖ ≤ L x ^ Cf →
          ‖frequencyDyad P G x U Z lo hi rho sigma xi N r k c alpha‖ ≤ Kmain * Z * L x ^ (-D) := by
        intro xi hxi
        have hframe' (chi : DirichletCharacter ℂ r) :=
          hframe U lo hi rho sigma tau eta xi c alpha r hr chi htau htaueta heta
            hlo hlohi hhi hcoef hrough hrho hsigma hxi hrCZ
        have hEbounds : ∀ chi : DirichletCharacter ℂ r,
            EndpointBound x Ce tau eta (shiftEndpoint U lo hi rho sigma (-2 * Real.pi * xi 1) c alpha r hr chi) ∧
            EndpointBound x Ce tau eta (shiftEndpoint U lo hi rho sigma (2 * Real.pi * xi 0) c alpha r hr chi) :=
          fun chi => ⟨(hframe' chi).1, (hframe' chi).2.1⟩
        exact hfreq G U Z lo hi rho sigma xi N r hr k c alpha hG hUpos hZpos hNcover hEbounds
          hk hkCe hZlo hZhi (hframe' 1).2.2.1 (hframe' 1).2.2.2 hroughfree hunit hdisc
      have habs' := habs G U Z lo hi rho sigma N k dyadicCutoff c alpha hG hUpos hZ1 hZsquare
        (hkCe.trans hZshift) dyadicCutoff_support abs_dyadicCutoff_le_one hcoef hrough
      have hnorm := determinantAtShift_power_bound P G x E U V Z lo hi rho sigma Cf Kf D At Ct
        Kmain Kat Ktail N k etae etan c alpha a hk hUpos hZpos hLpos hKmain.le hKat.le hKtail.le
        ha hFa hL1a htail hmain habs'
      have hexp : Kf - D = -(A + 2 * Ce + 2) := by dsimp [D]; ring
      have hexptail : Ct - At = -(A + 2 * Ce + 2) := by dsimp [At]; ring
      rw [hexp, hexptail] at hnorm
      apply hnorm.trans_eq
      dsimp [Ktotal]
      ring


end Erdos821.P6Off
