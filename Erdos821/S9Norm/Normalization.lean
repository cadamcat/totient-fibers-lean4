import Erdos821.S9.NormalizationTask
import Erdos821.P7.HarmonicPLower

noncomputable section
open Filter
namespace Erdos821.S9Norm
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

private theorem mertens_sieveProduct_bounds (hc : ClassicalInputs) :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ y : ℝ in atTop, c / 2 < Real.log y * sieveProduct y) ∧
      (∀ᶠ y : ℝ in atTop, Real.log y * sieveProduct y < 3 * c / 2) := by
  let c : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have hcpos : 0 < c := Real.exp_pos _
  have hlow : ∀ᶠ y : ℝ in atTop, c / 2 < Real.log y * sieveProduct y :=
    hc.mertens.2.eventually
      (eventually_gt_nhds (by dsimp [c]; linarith [Real.exp_pos (-Real.eulerMascheroniConstant)]))
  have hhigh : ∀ᶠ y : ℝ in atTop, Real.log y * sieveProduct y < 3 * c / 2 :=
    hc.mertens.2.eventually
      (eventually_lt_nhds (by dsimp [c]; linarith [Real.exp_pos (-Real.eulerMascheroniConstant)]))
  exact ⟨c, hcpos, hlow, hhigh⟩

private theorem main_constant_identity (K cZ cmin ell : ℝ)
    (hell : ell ≠ 0) (hcmin : cmin ≠ 0) :
    K * (cZ / ell) = (K * cZ / cmin) * cmin / ell := by
  field_simp [hell, hcmin]
  <;> ring

private theorem main_factor_identity (Kmain cmin x ell q p w : ℝ)
    (hell : ell ≠ 0) :
    (Kmain * cmin / ell) * (x * w ^ 2 * q * p) =
      Kmain * ((cmin * (x / ell) * q * p) * w ^ 2) := by
  field_simp [hell]
  <;> ring

private theorem base_factor_identity (cmin cW x ell q : ℝ)
    (hell : ell ≠ 0) :
    cmin * cW * (x / ell ^ 2) * q = (cmin * (x / ell) * q) * (cW / ell) := by
  field_simp [hell]
  <;> ring

private theorem error_factor_identity (K cmin cW x ell q : ℝ)
    (hell : ell ≠ 0) (hcmin : cmin ≠ 0) (hcW : cW ≠ 0) :
    K * ((x / ell ^ 2) * q) =
      (K / (cmin * cW)) * (cmin * cW * (x / ell ^ 2) * q) := by
  field_simp [hell, hcmin, hcW]
  <;> ring

private theorem log_power_error_scale (x l A : ℝ) (hx : 0 < x) (hl : 0 < l)
    (hsmall : l ^ (A + 2) / x ^ (9 / 25 : ℝ) < 1) :
    x ^ (0.64 : ℝ) * l ^ A ≤ x / l ^ (2 : ℝ) := by
  have hpow : l ^ (A + 2) < x ^ (9 / 25 : ℝ) := by
    simpa only [one_mul] using
      (div_lt_iff₀ (Real.rpow_pos_of_pos hx (9 / 25 : ℝ))).1 hsmall
  have hlogid : l ^ A * l ^ (2 : ℝ) = l ^ (A + 2) := by
    rw [← Real.rpow_add hl]
  have hpowProd : x ^ (16 / 25 : ℝ) * x ^ (9 / 25 : ℝ) = x := by
    calc
      _ = x ^ ((16 / 25 : ℝ) + (9 / 25 : ℝ)) :=
        (Real.rpow_add hx _ _).symm
      _ = x := by norm_num
  have hmul : x ^ (16 / 25 : ℝ) * l ^ A * l ^ (2 : ℝ) ≤ x := by
    calc
      _ = x ^ (16 / 25 : ℝ) * (l ^ A * l ^ (2 : ℝ)) := by ring
      _ = x ^ (16 / 25 : ℝ) * l ^ (A + 2) := by rw [hlogid]
      _ ≤ x ^ (16 / 25 : ℝ) * x ^ (9 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow.le (Real.rpow_nonneg hx.le _)
      _ = x := hpowProd
  have hxpow : x ^ (0.64 : ℝ) = x ^ (16 / 25 : ℝ) := by
    congr 1
    norm_num
  have hmul' : x ^ (0.64 : ℝ) * l ^ A * l ^ (2 : ℝ) ≤ x := by
    simpa only [hxpow] using hmul
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hl (2 : ℝ))).2 hmul'

set_option maxHeartbeats 1000000 in
theorem BalancedNormalizationTask_proof : Erdos821.S56Core.BalancedNormalizationTask := by
  intro hc δ C hC hBounds A K hK
  obtain ⟨c, hcpos, hMlower, hMupper⟩ := mertens_sieveProduct_bounds hc
  obtain ⟨_, CA, cmin, cmax, hKbounds, hcmin, hcmax, hbounds⟩ := hBounds
  have hHPall := Erdos821.P7Core.geometry_harmonicP_ge_one C δ hC
  rcases hC with
    ⟨hBand, _, hC₂, _, _, _, _, _, _, _, _, _, _, _, _, _, hθlower, _, _, _, _, _, _, _⟩
  rcases hBand with ⟨_, _, _, hs', _⟩
  have hC₂pos : 0 < C.bands.c₂ := by rw [hC₂]; norm_num
  have hθ : 0 < C.theta := by
    have hleft : 0 < C.bands.c₂ * C.bands.s' / 2 ^ C.micro := by positivity
    exact hleft.trans hθlower
  have hcZ : 0 < (3 * c / 2) / C.theta := div_pos (by positivity) hθ
  let cZ : ℝ := (3 * c / 2) / C.theta
  let cW : ℝ := (c / 2) ^ 2
  let Kmain : ℝ := K * cZ / cmin
  let Kerr : ℝ := K / (cmin * cW)
  let K' : ℝ := Kmain + Kerr
  have hcW : 0 < cW := by dsimp [cW]; positivity
  have hKmain : 0 < Kmain := by dsimp [Kmain]; positivity
  have hKerr : 0 < Kerr := by dsimp [Kerr]; positivity
  have hK' : 0 < K' := by dsimp [K']; positivity
  have hL : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hz : Tendsto (fun x : ℝ => x ^ C.theta) atTop atTop := tendsto_rpow_atTop hθ
  have hW : Tendsto (fun x : ℝ => Erdos821.Blueprint.Analytic.W x) atTop atTop := by
    change Tendsto (fun x : ℝ => Real.exp (Real.sqrt (Real.log x))) atTop atTop
    exact Real.tendsto_exp_atTop.comp (Real.tendsto_sqrt_atTop.comp hL)
  have hMz : ∀ᶠ x : ℝ in atTop,
      Real.log (x ^ C.theta) * sieveProduct (x ^ C.theta) < 3 * c / 2 :=
    hz.eventually hMupper
  have hMw : ∀ᶠ x : ℝ in atTop,
      c / 2 < Real.log (Erdos821.Blueprint.Analytic.W x) * sieveProduct (Erdos821.Blueprint.Analytic.W x) :=
    hW.eventually hMlower
  have hlogAbsorb : Tendsto
      (fun x : ℝ => Erdos821.Blueprint.Analytic.L x ^ (A + 2) / x ^ (9 / 25 : ℝ)) atTop (nhds 0) := by
    simpa [L] using
      (isLittleO_log_rpow_rpow_atTop (A + 2) (by norm_num : (0 : ℝ) < 9 / 25)).tendsto_div_nhds_zero
  have hlogAbsorb' : ∀ᶠ x : ℝ in atTop,
      Erdos821.Blueprint.Analytic.L x ^ (A + 2) / x ^ (9 / 25 : ℝ) < 1 :=
    hlogAbsorb.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨K', hK', ?_⟩
  intro j hj
  have hmassEvent := hbounds j hj
  filter_upwards [hMz, hMw, hHPall, hmassEvent, hlogAbsorb',
    eventually_gt_atTop (1 : ℝ), hL.eventually (eventually_ge_atTop (1 : ℝ))]
    with x hMzx hMwx hHP hmx hlogsmall hx hLx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Erdos821.Blueprint.Analytic.L x := by
    change 0 < Real.log x
    exact lt_of_lt_of_le (by norm_num) hLx
  have hthetaLog : Real.log (x ^ C.theta) = C.theta * Erdos821.Blueprint.Analytic.L x := by
    rw [Real.log_rpow hxpos]
    rfl
  have hMzx' : C.theta * Erdos821.Blueprint.Analytic.L x * sieveProduct (x ^ C.theta) < 3 * c / 2 := by
    simpa only [hthetaLog] using hMzx
  have hdenZ : 0 < C.theta * Erdos821.Blueprint.Analytic.L x := mul_pos hθ hLpos
  have hVz' : sieveProduct (x ^ C.theta) < (3 * c / 2) / (C.theta * Erdos821.Blueprint.Analytic.L x) :=
    (lt_div_iff₀ hdenZ).2 (by nlinarith only [hMzx'])
  have hVz : sieveProduct (x ^ C.theta) ≤ cZ / Erdos821.Blueprint.Analytic.L x := by
    have hid : (3 * c / 2) / (C.theta * Erdos821.Blueprint.Analytic.L x) = cZ / Erdos821.Blueprint.Analytic.L x := by
      dsimp [cZ]
      field_simp [ne_of_gt hθ, ne_of_gt hLpos]
      <;> ring
    rw [hid] at hVz'
    exact hVz'.le
  have hsqrtPos : 0 < Real.sqrt (Erdos821.Blueprint.Analytic.L x) := Real.sqrt_pos.2 hLpos
  have hWlog : Real.log (Erdos821.Blueprint.Analytic.W x) = Real.sqrt (Erdos821.Blueprint.Analytic.L x) := by
    simp [W]
  have hMwx' : c / 2 < Real.sqrt (Erdos821.Blueprint.Analytic.L x) * sieveProduct (Erdos821.Blueprint.Analytic.W x) := by
    simpa only [hWlog] using hMwx
  have hrootVpos : 0 < Real.sqrt (Erdos821.Blueprint.Analytic.L x) * sieveProduct (Erdos821.Blueprint.Analytic.W x) := by
    linarith [hcpos]
  have hhalfSq : cW < Erdos821.Blueprint.Analytic.L x * sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2 := by
    change (c / 2) ^ 2 < Erdos821.Blueprint.Analytic.L x *
      sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2
    have hhalf : 0 < c / 2 := by positivity
    have hleft : (c / 2) * (c / 2) < (c / 2) *
        (Real.sqrt (Erdos821.Blueprint.Analytic.L x) * sieveProduct (Erdos821.Blueprint.Analytic.W x)) :=
      mul_lt_mul_of_pos_left hMwx' hhalf
    have hright : (c / 2) * (Real.sqrt (Erdos821.Blueprint.Analytic.L x) * sieveProduct (Erdos821.Blueprint.Analytic.W x)) <
        (Real.sqrt (Erdos821.Blueprint.Analytic.L x) * sieveProduct (Erdos821.Blueprint.Analytic.W x)) *
          (Real.sqrt (Erdos821.Blueprint.Analytic.L x) * sieveProduct (Erdos821.Blueprint.Analytic.W x)) :=
      mul_lt_mul_of_pos_right hMwx' hrootVpos
    have hsq : (c / 2) ^ 2 <
        (Real.sqrt (Erdos821.Blueprint.Analytic.L x) * sieveProduct (Erdos821.Blueprint.Analytic.W x)) ^ 2 := by
      nlinarith only [hleft, hright]
    have hsq' : (Real.sqrt (Erdos821.Blueprint.Analytic.L x) * sieveProduct (Erdos821.Blueprint.Analytic.W x)) ^ 2 =
        Erdos821.Blueprint.Analytic.L x * sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hLpos.le]
    calc
      (c / 2) ^ 2 <
          (Real.sqrt (Erdos821.Blueprint.Analytic.L x) *
            sieveProduct (Erdos821.Blueprint.Analytic.W x)) ^ 2 := hsq
      _ = Erdos821.Blueprint.Analytic.L x *
          sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2 := hsq'
  have hVw : cW / Erdos821.Blueprint.Analytic.L x ≤ sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2 :=
    (div_le_iff₀ hLpos).2 (by simpa [mul_comm] using hhalfSq.le)
  rcases hmx with ⟨hmassBase, hmassLower, hmassUpper, _⟩
  let qx : ℝ := C.bands.harmonicQ x j
  let px : ℝ := C.bands.harmonicP x
  let massx : ℝ := C.mass x j
  let wx : ℝ := sieveProduct (Erdos821.Blueprint.Analytic.W x)
  let zx : ℝ := sieveProduct (x ^ C.theta)
  have hpx : 1 ≤ px := by simpa [px] using hHP
  have hmasspos : 0 < massx := by
    have hbasepos : 0 < x * Erdos821.Blueprint.Analytic.L x ^ (-CA) :=
      mul_pos hxpos (Real.rpow_pos_of_pos hLpos _)
    exact hbasepos.trans_le (by simpa [massx] using hmassBase)
  have hmassUpper' : massx ≤ (cmax * (x / Erdos821.Blueprint.Analytic.L x)) * (qx * px) := by
    simpa [massx, qx, px, mul_assoc] using hmassUpper
  have hcoeffpos : 0 < cmax * (x / Erdos821.Blueprint.Analytic.L x) :=
    mul_pos hcmax (div_pos hxpos hLpos)
  have hqpxpos : 0 < qx * px := by
    have hprod : 0 < (cmax * (x / Erdos821.Blueprint.Analytic.L x)) * (qx * px) := by
      have := lt_of_lt_of_le hmasspos hmassUpper'
      nlinarith
    have hdiv := div_pos hprod hcoeffpos
    have hid : ((cmax * (x / Erdos821.Blueprint.Analytic.L x)) * (qx * px)) / (cmax * (x / Erdos821.Blueprint.Analytic.L x)) = qx * px := by
      field_simp [ne_of_gt hcoeffpos]
    rw [hid] at hdiv
    exact hdiv
  have hqxpos : 0 < qx := by
    by_contra hnot
    have hqxle : qx ≤ 0 := le_of_not_gt hnot
    have hpx0 : 0 ≤ px := le_trans (by norm_num) hpx
    have hprodle : qx * px ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hqxle hpx0
    linarith
  have hqxnonneg : 0 ≤ qx := hqxpos.le
  have hmassLower' : cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx * px ≤ massx := by
    simpa [massx, qx, px] using hmassLower
  have hmassV : (cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx * px) * wx ^ 2 ≤
      massx * wx ^ 2 :=
    mul_le_mul_of_nonneg_right hmassLower' (sq_nonneg wx)
  have hmainCoeff : 0 ≤ x * wx ^ 2 * qx * px :=
    mul_nonneg (mul_nonneg (mul_nonneg hxpos.le (sq_nonneg wx)) hqxpos.le)
      (le_trans (by norm_num) hpx)
  have hKz : K * zx ≤ Kmain * cmin / Erdos821.Blueprint.Analytic.L x := by
    calc
      K * zx ≤ K * (cZ / Erdos821.Blueprint.Analytic.L x) := mul_le_mul_of_nonneg_left (by simpa [zx] using hVz) hK.le
      _ = Kmain * cmin / Erdos821.Blueprint.Analytic.L x := by
        simpa [Kmain] using main_constant_identity K cZ cmin
          (Erdos821.Blueprint.Analytic.L x) hLpos.ne' hcmin.ne'
  have hmain : K * (x * wx ^ 2 * zx * qx * px) ≤
      Kmain * (massx * wx ^ 2) := by
    calc
      _ = (K * zx) * (x * wx ^ 2 * qx * px) := by ring
      _ ≤ (Kmain * cmin / Erdos821.Blueprint.Analytic.L x) * (x * wx ^ 2 * qx * px) :=
        mul_le_mul_of_nonneg_right hKz hmainCoeff
      _ = Kmain * ((cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx * px) * wx ^ 2) := by
        exact main_factor_identity Kmain cmin x (Erdos821.Blueprint.Analytic.L x)
          qx px wx hLpos.ne'
      _ ≤ Kmain * (massx * wx ^ 2) :=
        mul_le_mul_of_nonneg_left hmassV hKmain.le
  have hcoeff0 : 0 ≤ cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx :=
    mul_nonneg (mul_nonneg hcmin.le (div_nonneg hxpos.le hLpos.le)) hqxpos.le
  have hmassNoP : cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx ≤ massx := by
    calc
      _ = cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx * 1 := by ring
      _ ≤ cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx * px :=
        mul_le_mul_of_nonneg_left hpx hcoeff0
      _ ≤ massx := hmassLower'
  have hbase : cmin * cW * (x / Erdos821.Blueprint.Analytic.L x ^ (2 : ℝ)) * qx ≤ massx * wx ^ 2 := by
    calc
      _ = (cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx) * (cW / Erdos821.Blueprint.Analytic.L x) := by
        have hLsq : Erdos821.Blueprint.Analytic.L x ^ (2 : ℝ) =
            (Erdos821.Blueprint.Analytic.L x) ^ 2 :=
          Real.rpow_natCast (Erdos821.Blueprint.Analytic.L x) 2
        rw [hLsq]
        exact base_factor_identity cmin cW x (Erdos821.Blueprint.Analytic.L x)
          qx hLpos.ne'
      _ ≤ (cmin * (x / Erdos821.Blueprint.Analytic.L x) * qx) * wx ^ 2 :=
        mul_le_mul_of_nonneg_left hVw hcoeff0
      _ ≤ massx * wx ^ 2 :=
        mul_le_mul_of_nonneg_right hmassNoP (sq_nonneg wx)
  have hErrScale : x ^ (0.64 : ℝ) * Erdos821.Blueprint.Analytic.L x ^ A ≤ x / Erdos821.Blueprint.Analytic.L x ^ (2 : ℝ) := by
    exact log_power_error_scale x (Erdos821.Blueprint.Analytic.L x) A
      hxpos hLpos hlogsmall
  have herror : K * (x ^ (0.64 : ℝ) * Erdos821.Blueprint.Analytic.L x ^ A * qx) ≤
      Kerr * (massx * wx ^ 2) := by
    calc
      _ ≤ K * ((x / Erdos821.Blueprint.Analytic.L x ^ (2 : ℝ)) * qx) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hErrScale hqxnonneg
        · exact hK.le
      _ = Kerr * (cmin * cW * (x / Erdos821.Blueprint.Analytic.L x ^ (2 : ℝ)) * qx) := by
        have hLsq : Erdos821.Blueprint.Analytic.L x ^ (2 : ℝ) =
            (Erdos821.Blueprint.Analytic.L x) ^ 2 :=
          Real.rpow_natCast (Erdos821.Blueprint.Analytic.L x) 2
        rw [hLsq]
        simpa only [Kerr] using error_factor_identity K cmin cW x
          (Erdos821.Blueprint.Analytic.L x) qx hLpos.ne' hcmin.ne' hcW.ne'
      _ ≤ Kerr * (massx * wx ^ 2) :=
        mul_le_mul_of_nonneg_left hbase hKerr.le
  have hsum : K *
      (x * wx ^ 2 * zx * qx * px + x ^ (0.64 : ℝ) * Erdos821.Blueprint.Analytic.L x ^ A * qx) ≤
      K' * (massx * wx ^ 2) := by
    calc
      _ = K * (x * wx ^ 2 * zx * qx * px) +
          K * (x ^ (0.64 : ℝ) * Erdos821.Blueprint.Analytic.L x ^ A * qx) := by
        rw [mul_add]
      _ ≤ Kmain * (massx * wx ^ 2) + Kerr * (massx * wx ^ 2) :=
        add_le_add hmain herror
      _ = K' * (massx * wx ^ 2) := by
        have hcoeff : Kmain + Kerr = K' := by rfl
        calc
          _ = (Kmain + Kerr) * (massx * wx ^ 2) :=
            (add_mul Kmain Kerr (massx * wx ^ 2)).symm
          _ = K' * (massx * wx ^ 2) :=
            congrArg (fun a : ℝ => a * (massx * wx ^ 2)) hcoeff
  change K *
      (x * sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2 *
        sieveProduct (x ^ C.theta) * C.bands.harmonicQ x j * C.bands.harmonicP x +
        x ^ (0.64 : ℝ) * Erdos821.Blueprint.Analytic.L x ^ A *
          C.bands.harmonicQ x j) ≤
    K' * C.mass x j * sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2
  calc
    _ ≤ K' * (C.mass x j * sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2) := hsum
    _ = K' * C.mass x j * sieveProduct (Erdos821.Blueprint.Analytic.W x) ^ 2 :=
      (mul_assoc _ _ _).symm

end Erdos821.S9Norm

