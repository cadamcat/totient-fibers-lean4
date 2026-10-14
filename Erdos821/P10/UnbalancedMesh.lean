import Erdos821.S10.Tasks

/-! Finite exponent-mesh aggregation for the unbalanced P10 contribution. -/

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.P10
open Erdos821.Blueprint Erdos821.P7Core
attribute [local instance] Classical.propDecidable

theorem densityMeshPoint_bounds (b κ : ℝ) (N i : ℕ)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hbκ : b < κ) (hN : 0 < N) (hi : i ≤ N) :
    b ≤ densityMeshPoint b κ N i ∧
      densityMeshPoint b κ N i ≤ (1 / 2 : ℝ) - κ := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hiR : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
  have hratio0 : 0 ≤ (i : ℝ) / (N : ℝ) :=
    div_nonneg (by positivity) hNR.le
  have hratio1 : (i : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hNR]
    simpa using hiR
  have hcoef : 0 ≤ (1 / 2 : ℝ) - κ - b := by
    nlinarith [hκsmall, hbκ]
  constructor
  · dsimp [densityMeshPoint]
    nlinarith [mul_nonneg hcoef hratio0]
  · dsimp [densityMeshPoint]
    have hmul := mul_le_mul_of_nonneg_left hratio1 hcoef
    nlinarith

theorem densityMeshPoint_strict_mono (b κ : ℝ) (N i : ℕ)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hbκ : b < κ) (hN : 0 < N) :
    densityMeshPoint b κ N i < densityMeshPoint b κ N (i + 1) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcoef : 0 < (1 / 2 : ℝ) - κ - b := by
    nlinarith [hκsmall, hbκ]
  have hstep :
      densityMeshPoint b κ N (i + 1) - densityMeshPoint b κ N i =
        ((1 / 2 : ℝ) - κ - b) / (N : ℝ) := by
    dsimp [densityMeshPoint]
    push_cast
    ring
  have hpositive : 0 < ((1 / 2 : ℝ) - κ - b) / (N : ℝ) :=
    div_pos hcoef hNR
  linarith

theorem one_le_roughDensity_one (b : ℝ) (hb : 0 < b) :
    1 ≤ roughDensity b 1 := by
  have hterm (l : ℕ) : 0 ≤ densityTerm b 1 l := by
    unfold densityTerm
    apply MeasureTheory.integral_nonneg
    intro t
    change 0 ≤ if (∀ i, b ≤ t i) ∧ (∑ i, t i) ≤ 1 - b then
      (1 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0
    by_cases hdom : (∀ i, b ≤ t i) ∧ (∑ i, t i) ≤ 1 - b
    · have hden : 0 < 1 - ∑ i, t i := by linarith [hdom.2]
      have ht : ∀ i, 0 < t i := fun i => lt_of_lt_of_le hb (hdom.1 i)
      simp [hdom]
      have hprod : 0 < ∏ i, t i := by
        apply Finset.prod_pos
        intro i hi
        exact ht i
      positivity
    · simp [hdom]
  have hsum : 0 ≤
      ∑ l ∈ Finset.Icc 2 ⌊(1 : ℝ) / b⌋₊,
        densityTerm b 1 l / (l.factorial : ℝ) := by
    apply Finset.sum_nonneg
    intro l hl
    exact div_nonneg (hterm l) (by positivity)
  unfold roughDensity
  simp only [inv_one]
  linarith

set_option maxHeartbeats 5000000 in
theorem UnbalancedMeshTask_proof : UnbalancedMeshTask := by
  intro hc hs hII hp δ C hGeometry hBounds hTypeI
  intro b κ ε hb hbκ hκ hκsmall hε jstar hjstar hslot
  classical
  rcases hGeometry with
    ⟨hValid, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hPsi, hPsiSupport, _, _⟩
  have hBoundsFull : C.Bounds δ := hBounds
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩
  have hSingular : 0 < singularSeries := hp.products.1
  let R : ℝ := roughDensity b 1 - 1
  have hR : 0 ≤ R := by
    dsimp [R]
    have h := one_le_roughDensity_one b hb
    linarith
  let meshErr : ℝ := ε / 8
  have hMeshErr : 0 < meshErr := by dsimp [meshErr]; positivity
  let top : ℝ := (1 / 2 : ℝ) - κ
  have htopPos : 0 < top := by
    dsimp [top]
    linarith [hκsmall]
  have hbtop : b < top := by
    dsimp [top]
    nlinarith [hκsmall, hbκ]
  let logRange : ℝ := Real.log (top / b)
  have hlogRange : 0 < logRange := by
    dsimp [logRange]
    apply Real.log_pos
    exact (one_lt_div hb).2 hbtop
  let etaDensity : ℝ := meshErr / (2 * (logRange + 1))
  have hEtaDensity : 0 < etaDensity := by
    dsimp [etaDensity]
    positivity
  obtain ⟨N, hN, hDensitySupNonneg, hMeshRaw⟩ :=
    density_mesh_integral_bound hp b κ meshErr hb hκ hκsmall hbκ hMeshErr
  have hMesh :
      (∑ i ∈ Finset.range N,
        (densityMeshSup b κ N i + etaDensity) *
          Real.log (densityMeshPoint b κ N (i + 1) /
            densityMeshPoint b κ N i)) ≤ R + meshErr := by
    simpa [R, etaDensity, logRange, top, meshErr] using hMeshRaw
  let densityMass : ℝ :=
    ∑ i ∈ Finset.range N, (densityMeshSup b κ N i + etaDensity)
  have hDensityMassNonneg : 0 ≤ densityMass := by
    dsimp [densityMass]
    apply Finset.sum_nonneg
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    have hDi := hDensitySupNonneg i hi'
    linarith
  let etaRecip : ℝ := meshErr / (densityMass + 1)
  have hEtaRecip : 0 < etaRecip := by
    dsimp [etaRecip]
    positivity
  have hEtaRecipMass : etaRecip * densityMass ≤ meshErr := by
    have hden : 0 < densityMass + 1 := by linarith
    have hfrac : densityMass / (densityMass + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    calc
      etaRecip * densityMass =
          meshErr * (densityMass / (densityMass + 1)) := by
            dsimp [etaRecip]
            field_simp [ne_of_gt hden]
            <;> ring
      _ ≤ meshErr * 1 :=
        mul_le_mul_of_nonneg_left hfrac hMeshErr.le
      _ = meshErr := by ring
  let T : ℝ :=
    ∑ i ∈ Finset.range N,
      (densityMeshSup b κ N i + etaDensity) *
        (Real.log (densityMeshPoint b κ N (i + 1) /
          densityMeshPoint b κ N i) + etaRecip)
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    have hDi := hDensitySupNonneg i hi'
    have hleft := densityMeshPoint_bounds b κ N i hb hκ hκsmall hbκ hN
      (Nat.le_of_lt hi')
    have hright := densityMeshPoint_bounds b κ N (i + 1) hb hκ hκsmall
      hbκ hN (by omega)
    have hstrict := densityMeshPoint_strict_mono b κ N i hb hκ hκsmall
      hbκ hN
    have hleftPos : 0 < densityMeshPoint b κ N i :=
      lt_of_lt_of_le hb hleft.1
    have hlog : 0 < Real.log
        (densityMeshPoint b κ N (i + 1) / densityMeshPoint b κ N i) := by
      apply Real.log_pos
      exact (one_lt_div hleftPos).2 hstrict
    have hA : 0 ≤ densityMeshSup b κ N i + etaDensity := by linarith
    have hB : 0 ≤ Real.log
        (densityMeshPoint b κ N (i + 1) / densityMeshPoint b κ N i) +
          etaRecip := by linarith
    exact mul_nonneg hA hB
  have hTeq :
      T =
        (∑ i ∈ Finset.range N,
          (densityMeshSup b κ N i + etaDensity) *
            Real.log (densityMeshPoint b κ N (i + 1) /
              densityMeshPoint b κ N i)) + etaRecip * densityMass := by
    dsimp [T, densityMass]
    calc
      _ = ∑ i ∈ Finset.range N,
            ((densityMeshSup b κ N i + etaDensity) *
                Real.log (densityMeshPoint b κ N (i + 1) /
                  densityMeshPoint b κ N i) +
              (densityMeshSup b κ N i + etaDensity) * etaRecip) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = _ := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
        ring
  have hTbound : T ≤ R + 2 * meshErr := by
    rw [hTeq]
    linarith [hMesh, hEtaRecipMass]
  have hTdenom : T ≤ R + 2 * meshErr + 1 := by linarith
  have hSieveErrDenom : 0 < R + 3 * meshErr + 1 := by
    linarith [hR, hMeshErr]
  let etaRatio : ℝ :=
    singularSeries * meshErr / (R + 2 * meshErr + 1)
  have hEtaRatio : 0 < etaRatio := by
    dsimp [etaRatio]
    positivity
  have hEtaRatioT : etaRatio * T ≤ singularSeries * meshErr := by
    have hden : 0 < R + 2 * meshErr + 1 := by
      linarith [hR, hMeshErr]
    have hfrac : T / (R + 2 * meshErr + 1) ≤ 1 :=
      (div_le_one hden).2 hTdenom
    calc
      etaRatio * T =
          singularSeries * meshErr *
            (T / (R + 2 * meshErr + 1)) := by
              dsimp [etaRatio]
              field_simp [ne_of_gt hden]
              <;> ring
      _ ≤ singularSeries * meshErr * 1 :=
        mul_le_mul_of_nonneg_left hfrac
          (mul_nonneg hSingular.le hMeshErr.le)
      _ = singularSeries * meshErr := by ring
  have hBaseCoeff :
      (singularSeries + etaRatio) * T ≤
        singularSeries * (R + 3 * meshErr) := by
    calc
      (singularSeries + etaRatio) * T =
          singularSeries * T + etaRatio * T := by ring
      _ ≤ singularSeries * (R + 2 * meshErr) +
          singularSeries * meshErr := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hTbound hSingular.le)
              hEtaRatioT
      _ = singularSeries * (R + 3 * meshErr) := by ring
  let bstar : ℝ := b / 3
  have hbstar : 0 < bstar := by dsimp [bstar]; positivity
  have hbstarSmall : bstar < 1 / 2 := by
    dsimp [bstar]
    nlinarith [hbκ, hκsmall]
  have hbstarEq : b = 3 * bstar := by dsimp [bstar]; ring
  have hslot' :
      C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4 := by
    calc
      C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < b / 12 := hslot
      _ = bstar / 4 := by dsimp [bstar]; ring
  let etaBin : ℝ := singularSeries * meshErr / (N : ℝ)
  have hEtaBin : 0 < etaBin := by
    dsimp [etaBin]
    exact div_pos (mul_pos hSingular hMeshErr) (by exact_mod_cast hN)
  let theta : ℝ := (1 / 2 : ℝ) - κ / 2
  have htheta : theta < 1 / 2 := by dsimp [theta]; linarith
  let gamma (i : ℕ) : ℝ := densityMeshPoint b κ N i
  let gammaNext (i : ℕ) : ℝ := densityMeshPoint b κ N (i + 1)
  have hBinParams (i : ℕ) (hi : i < N) :
      ∃ B KII : ℝ, 0 < B ∧ 0 < KII ∧
        ∀ S : ℝ, 2 * B + 3 < S →
          ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
            ∀ h : ℕ, h₀ ≤ h → Even h →
              ∀ᶠ x : ℝ in atTop,
                (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
                    primeExponentBin (gamma i) (gammaNext i) x).filter
                      (fun z => z.2 ∣ 2 * z.1 + 1)),
                  C.weighted x jstar z.1 *
                    test (.rough (gamma i)) x
                      ((2 * z.1 + 1) / z.2)) ≤
                  (1 + Kblock * Real.exp (-(h : ℝ))) *
                      C.mass x jstar / Analytic.L x *
                        (roughBinDensitySup (gamma i) (gammaNext i) +
                          etaDensity) *
                        (singularSeries + etaRatio) *
                          (Real.log (gammaNext i / gamma i) + etaRecip) +
                    etaBin * C.mass x jstar / Analytic.L x := by
    have hleft := densityMeshPoint_bounds b κ N i hb hκ hκsmall hbκ hN
      (Nat.le_of_lt hi)
    have hright := densityMeshPoint_bounds b κ N (i + 1) hb hκ hκsmall
      hbκ hN (by omega)
    have hgamma : b ≤ gamma i := by simpa [gamma] using hleft.1
    have hgammapos : 0 < gamma i := lt_of_lt_of_le hb hgamma
    have hgammaprimeTop : gammaNext i ≤ (1 / 2 : ℝ) - κ := by
      simpa [gammaNext] using hright.2
    have hgammaStrict : gamma i < gammaNext i := by
      simpa [gamma, gammaNext] using
        densityMeshPoint_strict_mono b κ N i hb hκ hκsmall hbκ hN
    have hgammaTheta : gammaNext i < theta := by
      dsimp [theta]
      linarith [hgammaprimeTop, hκ]
    obtain ⟨B, KII, hB, hKII, hBin⟩ :=
      eventually_actual_prime_bin_density_bound_absorbed hc hs hII hp C δ
        hBoundsFull hTypeI hValid hPsi hPsiSupport jstar hjstar
        bstar b κ (gamma i) (gammaNext i) theta etaDensity etaRatio
        etaRecip etaBin hbstar hbstarSmall hbstarEq hslot'
        hb hκ hκsmall hgamma hgammaStrict hgammaprimeTop hgammaTheta
        htheta hEtaDensity hEtaRatio hEtaRecip hEtaBin
    refine ⟨B, KII, hB, hKII, ?_⟩
    intro S hS
    obtain ⟨Kblock, hKblock, h₀, hDepth⟩ := hBin S hS
    refine ⟨Kblock, hKblock, h₀, ?_⟩
    intro h hh heven
    filter_upwards [hDepth h hh heven] with x hx
    simpa [gamma, gammaNext, densityMeshSup, roughBinDensitySup] using hx
  classical
  choose B_i KII_i hB_i hKII_i hBinS using hBinParams
  let Bval (i : ℕ) : ℝ := if hi : i < N then B_i i hi else 0
  have hBvalEq (i : ℕ) (hi : i < N) : Bval i = B_i i hi := by
    simp [Bval, hi]
  have hBvalPos (i : ℕ) (hi : i < N) : 0 < Bval i := by
    rw [hBvalEq i hi]
    exact hB_i i hi
  let Bsum : ℝ := ∑ i ∈ Finset.range N, Bval i
  have hBval_le (i : ℕ) (hi : i < N) : Bval i ≤ Bsum := by
    dsimp [Bsum]
    apply Finset.single_le_sum
    · intro j hj
      exact (hBvalPos j (Finset.mem_range.mp hj)).le
    · exact Finset.mem_range.mpr hi
  have hBsum : 0 < Bsum := by
    have h0 : 0 < Bval 0 := hBvalPos 0 hN
    have h0le : Bval 0 ≤ Bsum := hBval_le 0 hN
    linarith
  let S : ℝ := 2 * Bsum + 4
  have hS_i (i : ℕ) (hi : i < N) : 2 * B_i i hi + 3 < S := by
    dsimp [S]
    have hBi : B_i i hi ≤ Bsum := by
      rw [← hBvalEq i hi]
      exact hBval_le i hi
    linarith
  have hPerBinDepth (i : ℕ) (hi : i < N) :
      ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
        ∀ h : ℕ, h₀ ≤ h → Even h →
          ∀ᶠ x : ℝ in atTop,
            (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
                primeExponentBin (gamma i) (gammaNext i) x).filter
                  (fun z => z.2 ∣ 2 * z.1 + 1)),
              C.weighted x jstar z.1 *
                test (.rough (gamma i)) x ((2 * z.1 + 1) / z.2)) ≤
              (1 + Kblock * Real.exp (-(h : ℝ))) *
                  C.mass x jstar / Analytic.L x *
                    (densityMeshSup b κ N i + etaDensity) *
                    (singularSeries + etaRatio) *
                      (Real.log (gammaNext i / gamma i) + etaRecip) +
                etaBin * C.mass x jstar / Analytic.L x := by
    rcases hBinS i hi S (hS_i i hi) with ⟨Kblock, hKblock, h₀, hdepth⟩
    refine ⟨Kblock, hKblock, h₀, ?_⟩
    intro h hh heven
    filter_upwards [hdepth h hh heven] with x hx
    simpa [gamma, gammaNext, densityMeshSup, roughBinDensitySup] using hx
  choose Kblock_i hBlockData using hPerBinDepth
  have hKblock_i (i : ℕ) (hi : i < N) : 0 < Kblock_i i hi :=
    (hBlockData i hi).1
  have hH0exists (i : ℕ) (hi : i < N) :
      ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → Even h →
        ∀ᶠ x : ℝ in atTop,
          (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
              primeExponentBin (gamma i) (gammaNext i) x).filter
                (fun z => z.2 ∣ 2 * z.1 + 1)),
            C.weighted x jstar z.1 *
              test (.rough (gamma i)) x ((2 * z.1 + 1) / z.2)) ≤
            (1 + Kblock_i i hi * Real.exp (-(h : ℝ))) *
                C.mass x jstar / Analytic.L x *
                  (densityMeshSup b κ N i + etaDensity) *
                  (singularSeries + etaRatio) *
                    (Real.log (gammaNext i / gamma i) + etaRecip) +
              etaBin * C.mass x jstar / Analytic.L x :=
    (hBlockData i hi).2
  choose h₀_i hDepth_i using hH0exists
  let Kval (i : ℕ) : ℝ := if hi : i < N then Kblock_i i hi else 0
  have hKvalEq (i : ℕ) (hi : i < N) : Kval i = Kblock_i i hi := by
    simp [Kval, hi]
  have hKvalPos (i : ℕ) (hi : i < N) : 0 < Kval i := by
    rw [hKvalEq i hi]
    exact hKblock_i i hi
  let Ksum : ℝ := ∑ i ∈ Finset.range N, Kval i
  have hKsumPos : 0 < Ksum := by
    have h0 : 0 < Kval 0 := hKvalPos 0 hN
    have h0le : Kval 0 ≤ Ksum := by
      dsimp [Ksum]
      apply Finset.single_le_sum
      · intro j hj
        exact (hKvalPos j (Finset.mem_range.mp hj)).le
      · exact Finset.mem_range.mpr hN
    linarith
  have hKi_le (i : ℕ) (hi : i < N) : Kval i ≤ Ksum := by
    dsimp [Ksum]
    apply Finset.single_le_sum
    · intro j hj
      exact (hKvalPos j (Finset.mem_range.mp hj)).le
    · exact Finset.mem_range.mpr hi
  let h₀val (i : ℕ) : ℕ := if hi : i < N then h₀_i i hi else 0
  have hh₀valEq (i : ℕ) (hi : i < N) : h₀val i = h₀_i i hi := by
    simp [h₀val, hi]
  let h₀sum : ℕ := ∑ i ∈ Finset.range N, h₀val i
  have hH0_le (i : ℕ) (hi : i < N) : h₀_i i hi ≤ h₀sum := by
    dsimp [h₀sum]
    rw [← hh₀valEq i hi]
    apply Finset.single_le_sum
    · intro j hj
      exact Nat.zero_le _
    · exact Finset.mem_range.mpr hi
  let expErr : ℝ := meshErr / (R + 3 * meshErr + 1)
  have hExpErr : 0 < expErr := by
    dsimp [expErr]
    positivity
  have hNatExp :
      Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ))) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    funext n
    simp [pow_one]
  have hSmallExp : ∀ᶠ n : ℕ in atTop,
      Ksum * ((n : ℝ) * Real.exp (-(n : ℝ))) < expErr := by
    have hscaled : Tendsto
        (fun n : ℕ => Ksum * ((n : ℝ) * Real.exp (-(n : ℝ))))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hNatExp
    exact hscaled.eventually (Iio_mem_nhds hExpErr)
  have hLarge : ∀ᶠ n : ℕ in atTop, max h₀sum 1 ≤ n :=
    eventually_ge_atTop (max h₀sum 1)
  obtain ⟨n, hnSmall, hnLarge⟩ := (hSmallExp.and hLarge).exists
  have hnOne : 1 ≤ n := le_trans (le_max_right h₀sum 1) hnLarge
  have h0leN : h₀sum ≤ n := le_trans (le_max_left h₀sum 1) hnLarge
  let depth : ℕ := 2 * n
  have h0depth : h₀sum ≤ depth := by dsimp [depth]; omega
  have hEvenDepth : Even depth := by
    refine ⟨n, ?_⟩
    dsimp [depth]
    omega
  have hnCast : 1 ≤ (n : ℝ) := by exact_mod_cast hnOne
  have hdepthCast : (depth : ℝ) = 2 * (n : ℝ) := by
    dsimp [depth]
    push_cast
    ring
  have hExpDepth : Real.exp (-(depth : ℝ)) ≤
      (n : ℝ) * Real.exp (-(n : ℝ)) := by
    rw [hdepthCast]
    calc
      Real.exp (-(2 * (n : ℝ))) ≤ Real.exp (-(n : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ (n : ℝ) * Real.exp (-(n : ℝ)) :=
        (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hnCast (Real.exp_pos _).le)
  have hKExp : Ksum * Real.exp (-(depth : ℝ)) ≤ expErr := by
    apply le_of_lt
    calc
      Ksum * Real.exp (-(depth : ℝ)) ≤
          Ksum * ((n : ℝ) * Real.exp (-(n : ℝ))) :=
            mul_le_mul_of_nonneg_left hExpDepth hKsumPos.le
      _ < expErr := hnSmall
  have hKExpR :
      Ksum * Real.exp (-(depth : ℝ)) * (R + 3 * meshErr) ≤ meshErr := by
    have hden : 0 < R + 3 * meshErr + 1 := hSieveErrDenom
    have hRpart : R + 3 * meshErr ≤ R + 3 * meshErr + 1 := by linarith
    calc
      Ksum * Real.exp (-(depth : ℝ)) * (R + 3 * meshErr) ≤
          Ksum * Real.exp (-(depth : ℝ)) *
            (R + 3 * meshErr + 1) :=
              mul_le_mul_of_nonneg_left hRpart
                (mul_nonneg hKsumPos.le (Real.exp_pos _).le)
      _ ≤ (meshErr / (R + 3 * meshErr + 1)) *
            (R + 3 * meshErr + 1) :=
              mul_le_mul_of_nonneg_right hKExp
                (le_of_lt hden)
      _ = meshErr := by field_simp [ne_of_gt hden]
  have hExpCoeff :
      (1 + Ksum * Real.exp (-(depth : ℝ))) *
          (singularSeries + etaRatio) * T ≤
        singularSeries * (R + 4 * meshErr) := by
    have hExtra :
        Ksum * Real.exp (-(depth : ℝ)) *
            ((singularSeries + etaRatio) * T) ≤
          singularSeries * meshErr := by
      calc
        _ ≤ Ksum * Real.exp (-(depth : ℝ)) *
              (singularSeries * (R + 3 * meshErr)) :=
                mul_le_mul_of_nonneg_left hBaseCoeff
                  (mul_nonneg hKsumPos.le (Real.exp_pos _).le)
        _ = singularSeries *
              (Ksum * Real.exp (-(depth : ℝ)) *
                (R + 3 * meshErr)) := by ring
        _ ≤ singularSeries * meshErr :=
              mul_le_mul_of_nonneg_left hKExpR hSingular.le
    calc
      _ = (singularSeries + etaRatio) * T +
            Ksum * Real.exp (-(depth : ℝ)) *
              ((singularSeries + etaRatio) * T) := by ring
      _ ≤ singularSeries * (R + 3 * meshErr) +
            singularSeries * meshErr := add_le_add hBaseCoeff hExtra
      _ = singularSeries * (R + 4 * meshErr) := by ring
  have hMassNonneg :
      ∀ᶠ x : ℝ in atTop, 0 ≤ C.mass x jstar / Analytic.L x := by
    have hX : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
    filter_upwards [hBound jstar hjstar, hX] with x hData hx
    rcases hData with ⟨hMassLower, _, _, _, _, _⟩
    have hx0 : 0 ≤ x := by linarith
    have hLpos : 0 < Analytic.L x := by
      dsimp [Analytic.L]
      exact Real.log_pos hx
    have hMass : 0 ≤ C.mass x jstar := by
      have hlower : 0 ≤ x * Analytic.L x ^ (-CA) :=
        mul_nonneg hx0 (Real.rpow_nonneg hLpos.le _)
      exact le_trans hlower hMassLower
    exact div_nonneg hMass hLpos.le
  let binMass (i : ℕ) (x : ℝ) : ℝ :=
    ∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
        primeExponentBin (gamma i) (gammaNext i) x).filter
          (fun z => z.2 ∣ 2 * z.1 + 1)),
      C.weighted x jstar z.1 *
        test (.rough (gamma i)) x ((2 * z.1 + 1) / z.2)
  have hBinEvents : ∀ᶠ x : ℝ in atTop, ∀ i : Fin N,
      binMass i.val x ≤
        (1 + Kval i.val * Real.exp (-(depth : ℝ))) *
            C.mass x jstar / Analytic.L x *
              (densityMeshSup b κ N i.val + etaDensity) *
              (singularSeries + etaRatio) *
                (Real.log (gammaNext i.val / gamma i.val) + etaRecip) +
                etaBin * C.mass x jstar / Analytic.L x := by
    apply eventually_all.2
    intro i
    have hi : i.val < N := i.isLt
    have hDepthBound : h₀_i i.val hi ≤ depth :=
      (hH0_le i.val hi).trans h0depth
    have hDepth := hDepth_i i.val hi depth hDepthBound hEvenDepth
    filter_upwards [hDepth] with x hx
    simpa [binMass, gamma, gammaNext, densityMeshSup, roughBinDensitySup,
      Kval, hi] using hx
  have hBinSumEvent : ∀ᶠ x : ℝ in atTop,
      unbalancedMeshMass C x jstar b κ N ≤
        singularSeries * (R + ε) * C.mass x jstar / Analytic.L x := by
    filter_upwards [hBinEvents, hMassNonneg] with x hBins hM
    let M : ℝ := C.mass x jstar / Analytic.L x
    have hMainSum :
        (∑ i ∈ Finset.range N,
          (1 + Kval i * Real.exp (-(depth : ℝ))) * M *
            (densityMeshSup b κ N i + etaDensity) *
            (singularSeries + etaRatio) *
            (Real.log (gammaNext i / gamma i) + etaRecip)) ≤
          M * (singularSeries * (R + 4 * meshErr)) := by
      have hqNonneg (i : ℕ) (_hi : i < N) :
          0 ≤ (densityMeshSup b κ N i + etaDensity) *
            (Real.log (gammaNext i / gamma i) + etaRecip) := by
        have hleft := densityMeshPoint_bounds b κ N i hb hκ hκsmall hbκ hN
          (Nat.le_of_lt _hi)
        have hstrict := densityMeshPoint_strict_mono b κ N i hb hκ hκsmall
          hbκ hN
        have hlog : 0 < Real.log (gammaNext i / gamma i) := by
          apply Real.log_pos
          apply (one_lt_div (lt_of_lt_of_le hb hleft.1)).2
          simpa [gamma, gammaNext] using hstrict
        have hDi := hDensitySupNonneg i _hi
        have hA : 0 ≤ densityMeshSup b κ N i + etaDensity := by linarith
        have hB : 0 ≤ Real.log (gammaNext i / gamma i) + etaRecip := by
          linarith
        exact mul_nonneg hA hB
      have hWeighted :
          (∑ i ∈ Finset.range N,
            (1 + Kval i * Real.exp (-(depth : ℝ))) *
              ((densityMeshSup b κ N i + etaDensity) *
                (Real.log (gammaNext i / gamma i) + etaRecip))) ≤
            (1 + Ksum * Real.exp (-(depth : ℝ))) * T := by
        calc
          _ ≤ ∑ i ∈ Finset.range N,
                (1 + Ksum * Real.exp (-(depth : ℝ))) *
                  ((densityMeshSup b κ N i + etaDensity) *
                    (Real.log (gammaNext i / gamma i) + etaRecip)) := by
                    apply Finset.sum_le_sum
                    intro i hi
                    have hi' : i < N := Finset.mem_range.mp hi
                    have hK := hKi_le i hi'
                    have hcoef :
                        1 + Kval i * Real.exp (-(depth : ℝ)) ≤
                          1 + Ksum * Real.exp (-(depth : ℝ)) := by
                      nlinarith [mul_le_mul_of_nonneg_right hK
                        (Real.exp_pos (-(depth : ℝ))).le]
                    exact mul_le_mul_of_nonneg_right hcoef
                      (hqNonneg i hi')
          _ = _ := by
            rw [Finset.mul_sum]
      have hSumEq :
          (∑ i ∈ Finset.range N,
            (1 + Kval i * Real.exp (-(depth : ℝ))) * M *
              (densityMeshSup b κ N i + etaDensity) *
              (singularSeries + etaRatio) *
              (Real.log (gammaNext i / gamma i) + etaRecip)) =
            M * (singularSeries + etaRatio) *
              (∑ i ∈ Finset.range N,
                (1 + Kval i * Real.exp (-(depth : ℝ))) *
                  ((densityMeshSup b κ N i + etaDensity) *
                    (Real.log (gammaNext i / gamma i) + etaRecip))) := by
        calc
          _ = ∑ i ∈ Finset.range N,
                M * (singularSeries + etaRatio) *
                  ((1 + Kval i * Real.exp (-(depth : ℝ))) *
                    ((densityMeshSup b κ N i + etaDensity) *
                      (Real.log (gammaNext i / gamma i) + etaRecip))) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
          _ = _ := by rw [Finset.mul_sum]
      calc
        _ = M * (singularSeries + etaRatio) *
              (∑ i ∈ Finset.range N,
                (1 + Kval i * Real.exp (-(depth : ℝ))) *
                  ((densityMeshSup b κ N i + etaDensity) *
                    (Real.log (gammaNext i / gamma i) + etaRecip))) := hSumEq
        _ ≤ M * (singularSeries + etaRatio) *
              ((1 + Ksum * Real.exp (-(depth : ℝ))) * T) := by
                apply mul_le_mul_of_nonneg_left hWeighted
                positivity
        _ = M * ((1 + Ksum * Real.exp (-(depth : ℝ))) *
              (singularSeries + etaRatio) * T) := by ring
        _ ≤ _ := by
              exact mul_le_mul_of_nonneg_left hExpCoeff hM
    have hErrorSum :
        (∑ i ∈ Finset.range N, etaBin * M) =
          M * (singularSeries * meshErr) := by
      have hNcast : (N : ℝ) ≠ 0 := by positivity
      calc
        _ = (etaBin * M) *
              (∑ i ∈ Finset.range N, (1 : ℝ)) := by
                rw [Finset.mul_sum]
                simp
        _ = (etaBin * M) * (N : ℝ) := by simp [Finset.card_range]
        _ = M * (singularSeries * meshErr) := by
              dsimp [etaBin]
              field_simp [hNcast]
              <;> ring
    have hsumBins :
        unbalancedMeshMass C x jstar b κ N ≤
          M * (singularSeries * (R + 4 * meshErr)) +
            M * (singularSeries * meshErr) := by
      change (∑ i ∈ Finset.range N, binMass i x) ≤ _
      calc
        _ ≤ ∑ i ∈ Finset.range N,
              ((1 + Kval i * Real.exp (-(depth : ℝ))) * M *
                  (densityMeshSup b κ N i + etaDensity) *
                  (singularSeries + etaRatio) *
                  (Real.log (gammaNext i / gamma i) + etaRecip) +
                etaBin * M) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  have hi' : i < N := Finset.mem_range.mp hi
                  have h := hBins ⟨i, hi'⟩
                  convert h using 1 <;> ring
        _ ≤ _ := by
              rw [Finset.sum_add_distrib]
              rw [show (∑ i ∈ Finset.range N,
                  (1 + Kval i * Real.exp (-(depth : ℝ))) * M *
                    (densityMeshSup b κ N i + etaDensity) *
                    (singularSeries + etaRatio) *
                    (Real.log (gammaNext i / gamma i) + etaRecip)) +
                ∑ i ∈ Finset.range N, etaBin * M =
                  (∑ i ∈ Finset.range N,
                    (1 + Kval i * Real.exp (-(depth : ℝ))) * M *
                      (densityMeshSup b κ N i + etaDensity) *
                      (singularSeries + etaRatio) *
                      (Real.log (gammaNext i / gamma i) + etaRecip)) +
                    (∑ i ∈ Finset.range N, etaBin * M) from rfl]
              exact add_le_add hMainSum hErrorSum.le
    have hCoeff :
        singularSeries * (R + 4 * meshErr) +
            singularSeries * meshErr =
          singularSeries * (R + 5 * meshErr) := by ring
    have hLast : R + 5 * meshErr ≤ R + ε := by
      dsimp [meshErr]
      linarith [hε]
    calc
      unbalancedMeshMass C x jstar b κ N ≤
          M * (singularSeries * (R + 4 * meshErr)) +
            M * (singularSeries * meshErr) := hsumBins
      _ = M * (singularSeries * (R + 5 * meshErr)) := by
        calc
          _ = M * (singularSeries * (R + 4 * meshErr) +
                singularSeries * meshErr) := by ring
          _ = _ := by rw [hCoeff]
      _ ≤ M * (singularSeries * (R + ε)) := by
        apply mul_le_mul_of_nonneg_left _ hM
        exact mul_le_mul_of_nonneg_left hLast hSingular.le
      _ = singularSeries * (R + ε) * C.mass x jstar / Analytic.L x := by
        dsimp [M]
        ring
  refine ⟨N, hN, ?_⟩
  filter_upwards [hBinSumEvent] with x hx
  simpa [R] using hx


end Erdos821.P10

namespace Erdos821.P7Core

/-- Finite mesh and per-bin error absorption for the unbalanced mass. -/
theorem UnbalancedMeshTask_proof : UnbalancedMeshTask :=
  Erdos821.P10.UnbalancedMeshTask_proof

example : UnbalancedMeshTask := UnbalancedMeshTask_proof


end Erdos821.P7Core

