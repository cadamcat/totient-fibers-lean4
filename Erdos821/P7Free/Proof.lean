import Erdos821.P7.FreeWindowTask
import Erdos821.P7Free.Window

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace Erdos821.P7Free
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P7Core

theorem freeWindowKernel_eq_finset_sum (C : CandidateData) (x : ℝ)
    (jstar : ℕ) (s : C.bands.Slot x) (v r : ℕ) :
    freeWindowKernel C x jstar s v r =
      ∑ p ∈ C.bands.slotValues x jstar s,
        (p : ℝ)⁻¹ * ((p : ℝ) * v * r) *
          C.psi (((p : ℝ) * v * r) / x) := by
  unfold freeWindowKernel
  exact (Finset.sum_coe_sort (C.bands.slotValues x jstar s)
    (fun p : ℕ => (p : ℝ)⁻¹ * ((p : ℝ) * v * r) * C.psi (((p : ℝ) * v * r) / x)))

theorem freeWindowKernel_eq_band_sum (C : CandidateData) (δ x : ℝ)
    (hC : C.Geometry δ) (jstar : ℕ) (hj : C.j₀ ≤ jstar)
    (s : C.bands.Slot x) (hs0 : s.1.val = 0) (v r : ℕ) :
    freeWindowKernel C x jstar s v r =
      ∑ p ∈ C.bands.band x 0,
        (p : ℝ)⁻¹ * ((p : ℝ) * v * r) *
          C.psi (((p : ℝ) * v * r) / x) := by
  rw [freeWindowKernel_eq_finset_sum,
    Erdos821.P7Core.zero_slotValues_eq_band C δ hC x jstar hj s hs0]

theorem FreeWindowBoundsTask_proof : Erdos821.P7Core.FreeWindowBoundsTask := by
  intro hPrime hPlace hc δ C hC
  obtain ⟨epsilon, sigma, hepsilon, hepsilon_lt, hsigma, hplacement⟩ :=
    hPlace δ C hC
  obtain ⟨kslot, Mslot, hkslot, hMslot, hfree⟩ :=
    Erdos821.P7Core.free_slot_harmonic_bounds hc C δ hC
  have hCcopy := hC
  rcases hCcopy with ⟨hD, hC1, hC2, hRatio, hsprime, hδsmall, hlastScale,
      hprefix, htail, hq, hell, hga, hgb, hgc, hgd, hmicro, htheta1, htheta2,
      htheta3, htheta4, hcont, hsupp, hpsi0, hpsiPos⟩
  have hc1pos : 0 < C.bands.c₁ := hD.2.1
  have hc12 : C.bands.c₁ < C.bands.c₂ := hD.2.2.1
  have hspos : 0 < C.bands.s' := hD.2.2.2.1
  have hc2pos : 0 < C.bands.c₂ := lt_trans hc1pos hc12
  obtain ⟨a, b, c, ha, hab, hb, hcpos, hpsiPos⟩ := hpsiPos
  have haPos : 0 < a := lt_trans zero_lt_one ha
  have hbPos : 0 < b := lt_trans haPos hab
  obtain ⟨B, hB, hBpsi⟩ :=
    Erdos821.P7Core.cutoff_bound C.psi hcont.continuous hsupp
  obtain ⟨uMin, uMax, huMin, huMax, hUEvent⟩ :=
    hPrime hc (1 : ℝ) 2 (by norm_num) (by norm_num)
  obtain ⟨lMin, lMax, hlMin, hlMax, hLEvent⟩ :=
    hPrime hc a b haPos hab
  obtain ⟨YU, hUEvent⟩ := Filter.eventually_atTop.1 hUEvent
  obtain ⟨YL, hLEvent⟩ := Filter.eventually_atTop.1 hLEvent
  let c1s : ℝ := C.bands.c₁ * C.bands.s'
  let c2s : ℝ := C.bands.c₂ * C.bands.s'
  have hc1s : 0 < c1s := by
    dsimp [c1s]
    exact mul_pos hc1pos hspos
  have hc2s : 0 < c2s := by
    dsimp [c2s]
    exact mul_pos hc2pos hspos
  have hlin : Tendsto (fun x : ℝ => c1s * L x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc1s).2 Erdos821.S56Core.tendsto_L
  have hexplin := Real.tendsto_exp_atTop.comp hlin
  have hExpYU : ∀ᶠ x : ℝ in atTop, 2 * YU ≤ Real.exp (c1s * L x) :=
    hexplin.eventually_ge_atTop (2 * YU)
  have hExpYL : ∀ᶠ x : ℝ in atTop, a * YL ≤ Real.exp (c1s * L x) :=
    hexplin.eventually_ge_atTop (a * YL)
  have hExp2a : ∀ᶠ x : ℝ in atTop, 2 * a ≤ Real.exp (c1s * L x) :=
    hexplin.eventually_ge_atTop (2 * a)
  have hLbig : ∀ᶠ x : ℝ in atTop, 2 * Real.log 2 ≤ c1s * L x :=
    hlin.eventually_ge_atTop (2 * Real.log 2)
  let denConst : ℝ := C.bands.c₂ * C.bands.s'
  have hdenConst : 0 < denConst := by
    dsimp [denConst]
    exact hc2s
  let kmin : ℝ := c * lMin / denConst
  let kmax : ℝ := 4 * B * uMax / c1s
  have hkmin : 0 < kmin := by
    dsimp [kmin]
    exact div_pos (mul_pos hcpos hlMin) hdenConst
  have hkmax : 0 < kmax := by
    dsimp [kmax]
    exact div_pos (by positivity) hc1s
  refine ⟨epsilon, sigma, kmin, kmax, hepsilon, hepsilon_lt, hsigma,
    hkmin, hkmax, ?_⟩
  intro jstar hj
  have hjpos : 0 < jstar := by omega
  have hplacementAt := hplacement a b ha hab hb jstar hj
  filter_upwards [hfree, hplacementAt, hExpYU, hExpYL, hExp2a, hLbig,
      Filter.eventually_gt_atTop (2 : ℝ)] with
      x hfreeX hplacementX hExpYU hExpYL hExp2a hLbig hx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := Real.log_pos (by linarith : 1 < x)
  have hscale0 : C.bands.scale x 0 = C.bands.s' * L x := by
    simp [BandData.scale]
  have hscaleLower : C.bands.c₁ * C.bands.scale x 0 = c1s * L x := by
    rw [hscale0]
    dsimp [c1s]
    ring
  have hscaleUpper : C.bands.c₂ * C.bands.scale x 0 = denConst * L x := by
    rw [hscale0]
    dsimp [denConst]
    ring
  intro s hs0 hs2 z r hr
  let V : ℕ := Erdos821.P7Core.restProduct C.bands z
  have hVpos : 0 < V := by
    dsimp [V]
    exact Erdos821.P7Core.restProduct_pos C.bands z
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hVposR : 0 < (V : ℝ) := by exact_mod_cast hVpos
  let d : ℝ := (V : ℝ) * (r : ℝ)
  have hdpos : 0 < d := by
    dsimp [d]
    exact mul_pos hVposR hrpos
  let y : ℝ := x / d
  have hypos : 0 < y := by
    dsimp [y]
    exact div_pos hxpos hdpos
  let kernelTerm : ℕ → ℝ := fun p =>
    (p : ℝ)⁻¹ * ((p : ℝ) * V * r) * C.psi (((p : ℝ) * V * r) / x)
  have hKernelBand : freeWindowKernel C x jstar s V r =
      ∑ p ∈ C.bands.band x 0, kernelTerm p := by
    simpa [kernelTerm] using
      (freeWindowKernel_eq_band_sum C δ x hC jstar hj s hs0 V r)
  have hkernelTermNonneg (p : ℕ) : 0 ≤ kernelTerm p := by
    dsimp [kernelTerm]
    apply mul_nonneg
    · apply mul_nonneg
      · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · positivity
    · exact hpsi0 _
  constructor
  · by_cases hhas : ∃ p : ℕ, p ∈ C.bands.band x 0 ∧
        C.psi (((p : ℝ) * V * r) / x) ≠ 0
    · rcases hhas with ⟨p, hpBand, hpPsi⟩
      have hWindowBounds (q : ℕ) (hqBand : q ∈ C.bands.band x 0)
          (hqPsi : C.psi (((q : ℝ) * V * r) / x) ≠ 0) :
          y ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * y := by
        have hsupportQ := hsupp hqPsi
        let U : ℝ := (q : ℝ) * V * r
        have hUlo : x ≤ U := by
          have h := (le_div_iff₀ hxpos).mp hsupportQ.1
          simpa [U] using h
        have hUhi : U ≤ 2 * x := by
          have h := (div_le_iff₀ hxpos).mp hsupportQ.2
          simpa [U] using h
        have hUeq : U = (q : ℝ) * d := by
          dsimp [U, d]
          ring
        constructor
        · have hxd : x ≤ (q : ℝ) * d := by simpa [hUeq] using hUlo
          have hdiv : x / d ≤ (q : ℝ) := (div_le_iff₀ hdpos).2 hxd
          simpa [y] using hdiv
        · have hqd : (q : ℝ) * d ≤ 2 * x := by
            calc
              (q : ℝ) * d = U := hUeq.symm
              _ ≤ 2 * x := hUhi
          calc
            (q : ℝ) ≤ (2 * x) / d := (le_div_iff₀ hdpos).2 hqd
            _ = 2 * y := by dsimp [y]; ring
      have hpPrime : p.Prime := (Finset.mem_filter.mp hpBand).2
      have hpBounds := hWindowBounds p hpBand hpPsi
      let WU : Finset ℕ :=
        (Finset.Icc ⌈(1 : ℝ) * y⌉₊ ⌊(2 : ℝ) * y⌋₊).filter Nat.Prime
      have hpWindow : p ∈ WU := by
        dsimp [WU]
        exact prime_mem_window_of_real_bounds p 1 2 y hpPrime
          (by simpa using hpBounds.1) (by simpa using hpBounds.2) (by positivity)
      have hpBandIcc := (Finset.mem_filter.mp hpBand).1
      have hpBandRange := Finset.mem_Icc.mp hpBandIcc
      have hpExpLo : Real.exp (c1s * L x) ≤ (p : ℝ) := by
        have h := Nat.ceil_le.mp hpBandRange.1
        rw [hscaleLower] at h
        exact h
      have hExp2y : Real.exp (c1s * L x) ≤ 2 * y := hpExpLo.trans hpBounds.2
      have hyYU : YU ≤ y := by
        have h := hExpYU.trans hExp2y
        linarith only [h]
      have hlog2y : c1s * L x ≤ Real.log (2 * y) :=
        (Real.le_log_iff_exp_le (mul_pos (by norm_num) hypos)).2 hExp2y
      have hlogMul : Real.log (2 * y) = Real.log 2 + Real.log y :=
        Real.log_mul (by norm_num) hypos.ne'
      rw [hlogMul] at hlog2y
      have hlogyLower : c1s * L x / 2 ≤ Real.log y := by
        linarith only [hLbig, hlog2y]
      have hlogyPos : 0 < Real.log y := by
        have hprod : 0 < c1s * L x := mul_pos hc1s hLpos
        linarith
      have hprimeUpper :
          (∑ q ∈ WU, (q : ℝ)⁻¹) ≤ uMax / Real.log y := by
        simpa [WU] using (hUEvent y hyYU).2
      have hrecipUpper : uMax / Real.log y ≤
          (2 * uMax) / (c1s * L x) := by
        apply (div_le_div_iff₀ hlogyPos (mul_pos hc1s hLpos)).2
        have hscaleLog : c1s * L x ≤ 2 * Real.log y := by
          nlinarith [hlogyLower]
        have hcross := mul_le_mul_of_nonneg_left hscaleLog (le_of_lt huMax)
        nlinarith [hcross]
      have htermUpper (q : ℕ) (hqBand : q ∈ C.bands.band x 0) :
          kernelTerm q ≤ if q ∈ WU then 2 * B * x * (q : ℝ)⁻¹ else 0 := by
        by_cases hqPsi : C.psi (((q : ℝ) * V * r) / x) = 0
        · by_cases hqWin : q ∈ WU
          · simp [kernelTerm, hqPsi, hqWin]
            positivity
          · simp [kernelTerm, hqPsi, hqWin]
        · have hqBounds := hWindowBounds q hqBand hqPsi
          have hqPrime : q.Prime := (Finset.mem_filter.mp hqBand).2
          have hqWindow : q ∈ WU := by
            dsimp [WU]
            exact prime_mem_window_of_real_bounds q 1 2 y hqPrime
              (by simpa using hqBounds.1) (by simpa using hqBounds.2) (by positivity)
          rw [if_pos hqWindow]
          have hsupportQ := hsupp hqPsi
          have hUhi : (q : ℝ) * V * r ≤ 2 * x := by
            have h := (div_le_iff₀ hxpos).mp hsupportQ.2
            simpa [Nat.cast_mul, mul_assoc] using h
          have hpsiNonneg : 0 ≤ C.psi (((q : ℝ) * V * r) / x) := hpsi0 _
          have hpsiBound : C.psi (((q : ℝ) * V * r) / x) ≤ B := hBpsi _
          have hinv : 0 ≤ (q : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
          have hfirst :
              (q : ℝ)⁻¹ * ((q : ℝ) * V * r) ≤ (q : ℝ)⁻¹ * (2 * x) :=
            mul_le_mul_of_nonneg_left hUhi hinv
          have hprod := mul_le_mul hfirst hpsiBound hpsiNonneg
            (mul_nonneg hinv (mul_nonneg (by norm_num) hxpos.le))
          dsimp [kernelTerm]
          calc
            (q : ℝ)⁻¹ * ((q : ℝ) * V * r) * C.psi (((q : ℝ) * V * r) / x)
                ≤ ((q : ℝ)⁻¹ * (2 * x)) * B := hprod
            _ = 2 * B * x * (q : ℝ)⁻¹ := by ring
      have hsumUpper :
          (∑ q ∈ C.bands.band x 0, kernelTerm q) ≤
            2 * B * x * (∑ q ∈ WU, (q : ℝ)⁻¹) := by
        calc
          _ ≤ ∑ q ∈ C.bands.band x 0,
                if q ∈ WU then 2 * B * x * (q : ℝ)⁻¹ else 0 := by
            apply Finset.sum_le_sum
            intro q hq
            exact htermUpper q hq
          _ = ∑ q ∈ (C.bands.band x 0).filter (fun q => q ∈ WU),
                2 * B * x * (q : ℝ)⁻¹ := by
            rw [← Finset.sum_filter]
          _ ≤ ∑ q ∈ WU, 2 * B * x * (q : ℝ)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro q hq
              exact (Finset.mem_filter.mp hq).2
            · intro q hq hqnot
              positivity
          _ = 2 * B * x * (∑ q ∈ WU, (q : ℝ)⁻¹) := by
            rw [← Finset.mul_sum]
      have hkernelUpper :
          freeWindowKernel C x jstar s V r ≤ kmax * (x / L x) := by
        calc
          freeWindowKernel C x jstar s V r ≤
              2 * B * x * (∑ q ∈ WU, (q : ℝ)⁻¹) := by
                rw [hKernelBand]
                exact hsumUpper
          _ ≤ 2 * B * x * (uMax / Real.log y) :=
                mul_le_mul_of_nonneg_left hprimeUpper (by positivity)
          _ ≤ 2 * B * x * ((2 * uMax) / (c1s * L x)) :=
                mul_le_mul_of_nonneg_left hrecipUpper (by positivity)
          _ = kmax * (x / L x) := by
                dsimp [kmax]
                field_simp [ne_of_gt hc1s, ne_of_gt hLpos]
                ring
      exact hkernelUpper
    · have hzero : (∑ p ∈ C.bands.band x 0, kernelTerm p) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hpsiZero : C.psi (((p : ℝ) * V * r) / x) = 0 := by
          by_contra hne
          exact hhas ⟨p, hp, hne⟩
        simp [kernelTerm, hpsiZero]
      rw [hKernelBand, hzero]
      positivity
  · intro hprefix hrbound
    have hslotMass := hfreeX jstar hj s hs0
    have hslotPos : 0 < Erdos821.P7Core.slotHarmonic C.bands x jstar s :=
      lt_of_lt_of_le hkslot hslotMass.1
    obtain ⟨vslot⟩ :=
      Erdos821.P7Core.slotValue_nonempty_of_harmonic_pos C.bands x jstar s hslotPos
    let zfull := Erdos821.P7Core.restoreList C.bands s vslot z
    have hprefixFull : Erdos821.P7Core.prefixMidpointEvent C epsilon s zfull := by
      simpa [zfull] using
        (Erdos821.P7Core.prefixMidpointEvent_restoreList C epsilon s vslot z).2 hprefix
    obtain ⟨hplaceLo, hplaceHi⟩ :=
      hplacementX s hs0 hs2 zfull hprefixFull r hr hrbound
    have houtside : Erdos821.P7Core.outsideSlotProduct C.bands zfull s = V := by
      simpa [zfull, V] using
        (Erdos821.P7Core.outsideSlotProduct_restoreList C.bands s vslot z)
    have hdplace : (r : ℝ) * (V : ℝ) = d := by
      dsimp [d]
      ring
    rw [houtside, hdplace] at hplaceLo hplaceHi
    have hplaceLoY :
        Real.exp (C.bands.c₁ * C.bands.scale x 0) ≤ a * y := by
      calc
        Real.exp (C.bands.c₁ * C.bands.scale x 0) ≤ (a * x) / d := hplaceLo
        _ = a * y := by dsimp [y]; field_simp [ne_of_gt hdpos]
    have hplaceHiY :
        b * y ≤ Real.exp (C.bands.c₂ * C.bands.scale x 0) := by
      calc
        b * y = (b * x) / d := by dsimp [y]; field_simp [ne_of_gt hdpos]
        _ ≤ Real.exp (C.bands.c₂ * C.bands.scale x 0) := hplaceHi
    have hplaceLoY' : Real.exp (c1s * L x) ≤ a * y := by
      simpa only [hscaleLower] using hplaceLoY
    have hmulYL : a * YL ≤ a * y := hExpYL.trans hplaceLoY'
    have hyYL : YL ≤ y := by
      have h := (le_div_iff₀ haPos).2 (by simpa [mul_comm] using hmulYL)
      simpa [mul_div_cancel_left₀ y haPos.ne'] using h
    have hmul2 : 2 * a ≤ a * y := hExp2a.trans hplaceLoY'
    have hyTwo : 2 ≤ y := by
      have h := (le_div_iff₀ haPos).2 (by simpa [mul_comm] using hmul2)
      simpa [mul_div_cancel_left₀ y haPos.ne'] using h
    have hlogyPos : 0 < Real.log y :=
      Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hyTwo)
    have hsubsetBand :
        (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime ⊆ C.bands.band x 0 :=
      prime_window_subset_band C.bands x a b y hplaceLoY hplaceHiY (by positivity)
    have hlogBy : Real.log (b * y) ≤ denConst * L x := by
      calc
        Real.log (b * y) ≤ Real.log (Real.exp (C.bands.c₂ * C.bands.scale x 0)) :=
          Real.log_le_log (mul_pos hbPos hypos) hplaceHiY
        _ = denConst * L x := by rw [Real.log_exp, hscaleUpper]
    have hlogMulBy : Real.log (b * y) = Real.log b + Real.log y :=
      Real.log_mul hbPos.ne' hypos.ne'
    rw [hlogMulBy] at hlogBy
    have hbgt1 : 1 < b := lt_trans ha hab
    have hlogbNonneg : 0 ≤ Real.log b := (Real.log_pos hbgt1).le
    have hlogyUpper : Real.log y ≤ denConst * L x :=
      (le_add_of_nonneg_left hlogbNonneg).trans hlogBy
    have hprimeLower :
        lMin / Real.log y ≤
          ∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime,
            (p : ℝ)⁻¹ := by
      exact (hLEvent y hyYL).1
    have hrecipLower : lMin / (denConst * L x) ≤ lMin / Real.log y := by
      apply (div_le_div_iff₀ (mul_pos hdenConst hLpos) hlogyPos).2
      have hcross := mul_le_mul_of_nonneg_left hlogyUpper hlMin.le
      exact hcross
    have htermLower (p : ℕ)
        (hp : p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime) :
        c * x * (p : ℝ)⁻¹ ≤ kernelTerm p := by
      have hpData := Finset.mem_filter.mp hp
      have hpRange := Finset.mem_Icc.mp hpData.1
      have hpLo : a * y ≤ (p : ℝ) := Nat.ceil_le.mp hpRange.1
      have hpHi : (p : ℝ) ≤ b * y :=
        (Nat.le_floor_iff (by positivity : 0 ≤ b * y)).mp hpRange.2
      have hpPrime : p.Prime := hpData.2
      let U : ℝ := (p : ℝ) * V * r
      have hUeq : U = (p : ℝ) * d := by
        dsimp [U, d]
        ring
      have hyD : y * d = x := by
        dsimp [y]
        exact div_mul_cancel₀ x hdpos.ne'
      have hUlo : a * x ≤ U := by
        calc
          a * x = a * (y * d) := by rw [hyD]
          _ = (a * y) * d := by ring
          _ ≤ (p : ℝ) * d := mul_le_mul_of_nonneg_right hpLo hdpos.le
          _ = U := hUeq.symm
      have hUhi : U ≤ b * x := by
        calc
          U = (p : ℝ) * d := hUeq
          _ ≤ (b * y) * d := mul_le_mul_of_nonneg_right hpHi hdpos.le
          _ = b * x := by rw [← hyD]; ring
      have hxLeAx : x ≤ a * x := by
        calc
          x = 1 * x := by ring
          _ ≤ a * x := mul_le_mul_of_nonneg_right (le_of_lt ha) hxpos.le
      have hxLeU : x ≤ U := hxLeAx.trans hUlo
      have hratioLo : a ≤ U / x := (le_div_iff₀ hxpos).2 hUlo
      have hratioHi : U / x ≤ b := (div_le_iff₀ hxpos).2 hUhi
      have hpsiLowerVal : c ≤ C.psi (U / x) :=
        hpsiPos (U / x) (Set.mem_Icc.mpr ⟨hratioLo, hratioHi⟩)
      have hinvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hpPrime.pos)
      have hInvU : (p : ℝ)⁻¹ * x ≤ (p : ℝ)⁻¹ * U :=
        mul_le_mul_of_nonneg_left hxLeU hinvPos.le
      have hlow1 : c * x * (p : ℝ)⁻¹ ≤ ((p : ℝ)⁻¹ * U) * c := by
        calc
          c * x * (p : ℝ)⁻¹ = ((p : ℝ)⁻¹ * x) * c := by ring
          _ ≤ ((p : ℝ)⁻¹ * U) * c := mul_le_mul_of_nonneg_right hInvU hcpos.le
      have hlow2 : ((p : ℝ)⁻¹ * U) * c ≤ ((p : ℝ)⁻¹ * U) * C.psi (U / x) :=
        mul_le_mul_of_nonneg_left hpsiLowerVal
          (mul_nonneg hinvPos.le (le_of_lt (lt_of_lt_of_le
            (mul_pos haPos hxpos) hUlo)))
      calc
        c * x * (p : ℝ)⁻¹ ≤ ((p : ℝ)⁻¹ * U) * c := hlow1
        _ ≤ ((p : ℝ)⁻¹ * U) * C.psi (U / x) := hlow2
        _ = kernelTerm p := by
          dsimp [kernelTerm, U]
    have hwindowLowerKernel :
        c * x *
            (∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime,
              (p : ℝ)⁻¹) ≤ freeWindowKernel C x jstar s V r := by
      calc
        _ = ∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime,
              c * x * (p : ℝ)⁻¹ := by rw [← Finset.mul_sum]
        _ ≤ ∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime,
              kernelTerm p := by
              apply Finset.sum_le_sum
              intro p hp
              exact htermLower p hp
        _ ≤ ∑ p ∈ C.bands.band x 0, kernelTerm p :=
              Finset.sum_le_sum_of_subset_of_nonneg hsubsetBand
                (fun p _ _ => hkernelTermNonneg p)
        _ = freeWindowKernel C x jstar s V r := hKernelBand.symm
    have hprimeLowerMul :
        c * x * (lMin / Real.log y) ≤ freeWindowKernel C x jstar s V r := by
      calc
        c * x * (lMin / Real.log y) ≤ c * x *
            (∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime,
              (p : ℝ)⁻¹) :=
                mul_le_mul_of_nonneg_left hprimeLower
                  (mul_nonneg hcpos.le hxpos.le)
        _ ≤ freeWindowKernel C x jstar s V r := hwindowLowerKernel
    calc
      kmin * (x / L x) = c * x * (lMin / (denConst * L x)) := by
        dsimp [kmin]
        field_simp [ne_of_gt hdenConst, ne_of_gt hLpos]
      _ ≤ c * x * (lMin / Real.log y) :=
        mul_le_mul_of_nonneg_left hrecipLower (mul_nonneg hcpos.le hxpos.le)
      _ ≤ freeWindowKernel C x jstar s V r := hprimeLowerMul

end Erdos821.P7Free

example : Erdos821.P7Core.FreeWindowBoundsTask :=
  @Erdos821.P7Free.FreeWindowBoundsTask_proof

