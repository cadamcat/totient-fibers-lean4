import Erdos821.S56.SmoothedCauchy
import Erdos821.S56.SplittingScale
import Erdos821.S56.Majorants
import Erdos821.S56.CoreBound
import Erdos821.P6Off.Proof

noncomputable section
open Filter
open scoped ContDiff

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem off_diagonal_shift : OffDiagonalShiftTask :=
  Erdos821.P6Off.offDiagonalShiftTask_proof

/-- The saving calculation after Cauchy. All logarithmic costs are fixed
before K0; the outside factor supplies L^(-K0). -/
theorem separated_saving (x U V A C Cd Kd Ko : ℝ)
    (ae ah alpha beta : ℕ → ℂ) (etae etan : ℝ → ℝ) (emin : ℝ)
    (hx : 0 < x) (hL : 1 ≤ L x) (hV : 1 ≤ V) (hU : 0 < U)
    (hUV : U * V ≤ 8 * x) (hA : 0 < A) (hC : 0 ≤ C)
    (hCd : 0 < Cd) (hKd : 0 < Kd) (hKo : 0 < Ko)
    (hemin : 1 ≤ emin)
    (hae : ∀ e, ‖ae e‖ ≤ L x ^ C) (hbeta : ∀ n, ‖beta n‖ ≤ L x ^ C)
    (hetae : ∀ y, 0 ≤ etae y) (hetan : ∀ y, 0 ≤ etan y)
    (hecover : ∀ e ∈ Finset.Icc ⌈emin⌉₊ ⌊U * L x ^ (-(4*C+Cd+2*A+1))⌋₊,
      1 ≤ etae (e / (U * L x ^ (-(4*C+Cd+2*A+1)))))
    (hncover : ∀ n ∈ dyad V, 1 ≤ etan (n / V))
    (hdiag : diagonalSum (U * L x ^ (-(4*C+Cd+2*A+1))) U V etae etan ah alpha ≤
      Kd * x * L x ^ Cd)
    (hoff : ‖offDiagonalSum (U * L x ^ (-(4*C+Cd+2*A+1))) U V etae etan ah alpha‖ ≤
      Ko * x * L x ^ (-1 : ℝ)) :
    ‖separatedSum emin (U * L x ^ (-(4*C+Cd+2*A+1))) U V ae ah alpha beta‖ ≤
      (16*(Kd+Ko)+1) * x * L x ^ (-A) := by
  have hLpos : 0 < L x := zero_lt_one.trans_le hL
  have hE : 0 < U * L x ^ (-(4*C+Cd+2*A+1)) := by positivity
  have hsq := smoothed_cauchy emin _ U V (L x ^ C) ae ah alpha beta etae etan
    hemin hE hV (by positivity) hae hbeta hetae hetan hecover hncover
  have hsmall : L x ^ (-1 : ℝ) ≤ L x ^ Cd :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hsquare : smoothedSquare (U * L x ^ (-(4*C+Cd+2*A+1))) U V etae etan ah alpha ≤
      (Kd+Ko) * x * L x ^ Cd := by
    rw [smoothed_square_eq]
    have hre := (Complex.re_le_norm _).trans hoff
    have ho := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hKo.le hx.le)
    calc
      _ ≤ Kd*x*L x^Cd + Ko*x*L x^(-1:ℝ) := add_le_add hdiag hre
      _ ≤ Kd*x*L x^Cd + Ko*x*L x^Cd := add_le_add le_rfl ho
      _ = _ := by ring
  have hfac : 2 * (U * L x ^ (-(4*C+Cd+2*A+1))) * V * (L x ^ C)^4 ≤
      16 * x * L x ^ (-(4*C+Cd+2*A+1)) * (L x ^ C)^4 := by
    have h := mul_le_mul_of_nonneg_right hUV
      (by positivity : 0 ≤ 2 * L x ^ (-(4*C+Cd+2*A+1)) * (L x ^ C)^4)
    convert h using 1 <;> ring
  have hsecond0 : 0 ≤ (Kd+Ko) * x * L x ^ Cd := by positivity
  have hpow : (L x ^ C)^4 = L x ^ (4*C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    congr 1
    ring
  have hcombine : (16*x*L x ^ (-(4*C+Cd+2*A+1))*(L x^C)^4) *
      ((Kd+Ko)*x*L x^Cd) = 16*(Kd+Ko)*x^2*L x^(-2*A-1) := by
    rw [hpow]
    rw [show -2*A-1 = -(4*C+Cd+2*A+1)+(4*C)+Cd by ring,
      Real.rpow_add hLpos, Real.rpow_add hLpos]
    ring
  have hbound : ‖separatedSum emin (U * L x ^ (-(4*C+Cd+2*A+1))) U V ae ah alpha beta‖^2 ≤
      16*(Kd+Ko)*(x*L x^(-A))^2 := by
    calc
      _ ≤ _ := hsq
      _ ≤ (16*x*L x ^ (-(4*C+Cd+2*A+1))*(L x^C)^4)*((Kd+Ko)*x*L x^Cd) :=
        (mul_le_mul_of_nonneg_left hsquare (by positivity)).trans
          (mul_le_mul_of_nonneg_right hfac hsecond0)
      _ = 16*(Kd+Ko)*x^2*L x^(-2*A-1) := hcombine
      _ ≤ 16*(Kd+Ko)*x^2*L x^(-2*A) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)
      _ = _ := by
        have hp2 : (L x^(-A))^2 = L x^(-2*A) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
          congr 1
          ring
        rw [mul_pow, hp2]
        ring
  have hconstant : 16*(Kd+Ko) ≤ (16*(Kd+Ko)+1)^2 := by nlinarith [sq_nonneg (Kd+Ko)]
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_right hconstant (sq_nonneg (x*L x^(-A))))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow, mul_assoc] using hbound'

/-- Uniform separated estimate, with splitting precision chosen after the
coefficient, mark and majorant costs and before discrepancy precision B. -/
theorem separated_estimate (hc : ClassicalInputs) (hshift : ShiftEstimate)
    (P : Geometry) (A b C0 Cs tau eta : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hC0 : 0 < C0) (hCs : 0 < Cs)
    (htau : 0 < tau) (htaueta : tau < eta) (heta : eta < 1/4) (hetab : eta < b/4) :
    ∃ K0 B K : ℝ, 0 < K0 ∧ 0 < B ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (U V lo hi rho sigma : ℝ) (ae c alpha beta : ℕ → ℂ),
        Admissible P x G → x/8 ≤ U*V → U*V ≤ 8*x →
        x^b ≤ U → U ≤ x^(1-b) → x^b ≤ V → V ≤ x^(1-b) →
        x^tau ≤ lo → lo ≤ hi → hi ≤ x^eta →
        |rho| ≤ L x^C0 → |sigma| ≤ L x^C0 →
        (∀ n, ‖ae n‖ ≤ L x^C0 ∧ ‖c n‖ ≤ L x^C0 ∧
          ‖alpha n‖ ≤ L x^C0 ∧ ‖beta n‖ ≤ L x^C0) →
        (∀ n, alpha n ≠ 0 → rough (W x) n) →
        discrepancy x B (restricted U alpha) →
        ‖separatedSum (U*L x^(-K0)*L x^(-Cs)) (U*L x^(-K0)) U V ae
          (hCoefficient P G x lo hi rho sigma c) alpha beta‖ ≤ K*x*L x^(-A) := by
  obtain ⟨Cm, hCm, hm⟩ := Erdos821.P6Sq.markWeight_log_bound P
  obtain ⟨Cmaj, hCmaj, bounds, hbounds, hmaj⟩ := dyadic_majorants Cs hCs
  let C := C0 + Cm + Cmaj + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0C : C0 ≤ C := by dsimp [C]; linarith
  have hCmajC : Cmaj ≤ C := by dsimp [C]; linarith
  have hCmC : Cm+C0 ≤ C := by dsimp [C]; linarith
  obtain ⟨Cd, Kd, hCd, hKd, hd⟩ := diagonal_polylog hc C hC.le
  let K0 := 4*C+Cd+2*A+1
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  obtain ⟨B, Ko, hB, hKo, ho⟩ := off_diagonal_shift hc hshift P 1 b C Cs K0 tau eta bounds
    (by norm_num) hb hC hCs hK0 htau htaueta heta hetab hbounds
  refine ⟨K0, B, 16*(Kd+Ko)+1, hK0, hB, by positivity, ?_⟩
  filter_upwards [hm, hmaj, hd, ho, eventually_splitting_scale b (K0+Cs) hb (by positivity),
    eventually_gt_atTop 1, tendsto_L.eventually (eventually_ge_atTop 1)]
    with x hm hmaj hd ho hscale hx hL
  intro G U V lo hi rho sigma ae c alpha beta hG hUVlo hUVhi hUlo hUhi hVlo hVhi
    hlo hlohi hhi hrho hsigma hcoeff hrough hdisc
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hLpos : 0 < L x := zero_lt_one.trans_le hL
  have hU : 1 ≤ U := (Real.one_le_rpow hx.le hb.le).trans hUlo
  have hV : 1 ≤ V := (Real.one_le_rpow hx.le hb.le).trans hVlo
  have hUC : 0 < U := zero_lt_one.trans_le hU
  have hpow : L x^C0 ≤ L x^C := Real.rpow_le_rpow_of_exponent_le hL hC0C
  have halpha : ∀ n, ‖alpha n‖ ≤ L x^C := fun n => (hcoeff n).2.2.1.trans hpow
  have hc0 : ∀ n, ‖c n‖ ≤ L x^C0 := fun n => (hcoeff n).2.1
  have hh : ∀ h : ℕ, 0 < h → ‖hCoefficient P G x lo hi rho sigma c h‖ ≤
      L x^C*(h.divisors.card : ℝ) := by
    intro h hh
    have hraw := hCoefficient_norm_bound P G x lo hi rho sigma (L x^C0) (L x^Cm) c
      (by positivity) (by positivity) hc0 (hm G hG) h hh
    have hprod : L x^Cm*L x^C0 ≤ L x^C := by
      rw [← Real.rpow_add hLpos]
      exact Real.rpow_le_rpow_of_exponent_le hL hCmC
    exact hraw.trans (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _))
  obtain ⟨etae, etan, hse, hsn, hsuppe, hsuppn, h01, heone, hnone, hderiv⟩ := hmaj
  have hd' := hd (U*L x^(-K0)) U V etae etan
    (hCoefficient P G x lo hi rho sigma c) alpha hU hV hUVhi
    (fun y => ⟨(h01 y).1, (h01 y).2.1⟩)
    (fun y => ⟨(h01 y).2.2.1, (h01 y).2.2.2⟩) halpha hh
  have hderiv' : ∀ j y, ‖iteratedDeriv j etae y‖ ≤ bounds j*L x^(C*(j+1)) ∧
      ‖iteratedDeriv j etan y‖ ≤ bounds j*L x^(C*(j+1)) := by
    intro j y
    have hp := Real.rpow_le_rpow_of_exponent_le hL
      (mul_le_mul_of_nonneg_right hCmajC (by positivity : (0:ℝ) ≤ j+1))
    have hh := mul_le_mul_of_nonneg_left hp (hbounds j)
    exact ⟨(hderiv j y).1.trans hh, (hderiv j y).2.trans hh⟩
  have ho' := ho G U V lo hi rho sigma c alpha etae etan hG hUVlo hUVhi hUlo hUhi hVlo hVhi
    hlo hlohi hhi (hrho.trans hpow) (hsigma.trans hpow)
    (fun n => ⟨halpha n, (hc0 n).trans hpow⟩) hrough hdisc hse hsn hsuppe hsuppn hderiv'
  have hE : 0 < U*L x^(-K0) := by positivity
  have hemin : 1 ≤ U*L x^(-K0)*L x^(-Cs) := by
    have hs := hscale U hUlo
    rwa [show -(K0+Cs) = -K0 + -Cs by ring, Real.rpow_add hLpos, ← mul_assoc] at hs
  have hecover : ∀ e ∈ Finset.Icc ⌈U*L x^(-K0)*L x^(-Cs)⌉₊ ⌊U*L x^(-K0)⌋₊,
      1 ≤ etae (e/(U*L x^(-K0))) := by
    intro e he
    have helo := Nat.ceil_le.mp (Finset.mem_Icc.mp he).1
    have hehi := (Nat.le_floor_iff hE.le).mp (Finset.mem_Icc.mp he).2
    have hmem : (e:ℝ)/(U*L x^(-K0)) ∈ Set.Icc (L x^(-Cs)) 1 := by
      constructor
      · apply (le_div_iff₀ hE).mpr
        simpa [mul_comm] using helo
      · exact (div_le_one hE).mpr hehi
    rw [heone _ hmem]
  have hncover : ∀ n ∈ dyad V, 1 ≤ etan (n/V) := by
    intro n hn
    have hnlo := Nat.ceil_le.mp (Finset.mem_Ico.mp hn).1
    have hnhi := Nat.lt_ceil.mp (Finset.mem_Ico.mp hn).2
    have hmem : (n:ℝ)/V ∈ Set.Icc 1 2 := by
      constructor
      · exact (one_le_div (zero_lt_one.trans_le hV)).mpr hnlo
      · exact (div_le_iff₀ (zero_lt_one.trans_le hV)).mpr hnhi.le
    rw [hnone _ hmem]
  simpa only [K0] using separated_saving x U V A C Cd Kd Ko ae
    (hCoefficient P G x lo hi rho sigma c) alpha beta etae etan
    (U*L x^(-K0)*L x^(-Cs)) hxpos hL hV hUC hUVhi hA hC.le hCd hKd hKo hemin
    (fun n => (hcoeff n).1.trans hpow) (fun n => (hcoeff n).2.2.2.trans hpow)
    (fun y => (h01 y).1) (fun y => (h01 y).2.2.1) hecover hncover hd' ho'



end Erdos821.S56Core
