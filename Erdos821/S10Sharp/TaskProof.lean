import Erdos821.S10Sharp.Proof

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S10Sharp
open Erdos821.Blueprint Erdos821.P10 Erdos821.P7Core
attribute [local instance] Classical.propDecidable

/-- Choose the presieve exponent before the late slot. -/
theorem SharpPresieveTask_proof : SharpPresieveTask := by
  intro hc hs hp δ C hGeometry hBounds hTypeI bmax ε hbmax hε
  obtain ⟨Kdens, hKdens, hInterval⟩ := shifted_prime_density_interval_bound_all hc
  obtain ⟨Kblock, hKblock, h₀, hBlock⟩ :=
    hs.block (1 / 2) Kdens (by norm_num) hKdens
  have hBounds' := hBounds
  obtain ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩ := hBounds
  have hSing : 0 < singularSeries := hp.products.1
  have hMain : 0 < Real.exp (-Real.eulerMascheroniConstant) * singularSeries :=
    mul_pos (Real.exp_pos _) hSing
  let A : ℝ := Real.exp (-Real.eulerMascheroniConstant) * singularSeries
  have hA : 0 < A := hMain
  let η : ℝ := min (1 / 2) (ε / (16 * (A + 1)))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hηhalf : η ≤ 1 / 2 := min_le_left _ _
  have hηcap : η ≤ ε / (16 * (A + 1)) := min_le_right _ _
  let θ : ℝ := min (1 / 4) bmax
  have hθ : 0 < θ := lt_min (by norm_num) hbmax
  have hθhalf : θ < 1 / 2 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  obtain ⟨b, c, K, b₀, hdepth, hb, hbb₀, hcpos, hKpos, hb₀pos,
      hh₀, heven, hCut, hSieveError, hDensityError, hRough⟩ :=
    choose_presieve_parameters hp θ Kblock h₀ η η
      hθ hKblock hη hη
  have hb_lt_θ : b < θ := by
    have hdepth_nonneg : 0 ≤ (hdepth : ℝ) := Nat.cast_nonneg _
    have hfactor : (1 : ℝ) < 4 * (hdepth : ℝ) + 2 := by nlinarith
    have hmulPos : 0 < b * (4 * (hdepth : ℝ) + 2 - 1) :=
      mul_pos hb (by linarith)
    have hmul : b < b * (4 * (hdepth : ℝ) + 2) := by nlinarith [hmulPos]
    exact lt_trans hmul hCut
  have hb_lt_one : b < 1 := by
    have hθle : θ ≤ 1 / 4 := min_le_left _ _
    exact lt_of_lt_of_le hb_lt_θ (le_trans hθle (by norm_num))
  have hb_bmax : b < bmax := lt_of_lt_of_le hb_lt_θ (min_le_right _ _)
  refine ⟨b, hb, hb_bmax, ?_⟩
  intro jstar hjstar
  have hSieveLower := candidate_presieve_lower_of_witness hc hp C δ
    hBounds' hTypeI jstar hjstar Kdens Kblock hKdens hKblock
    hInterval h₀ hBlock b θ (ε / 4) (ε / 4) hb hθhalf
    (by positivity) (by positivity)
  have hSieveEvent := hSieveLower hdepth hh₀ heven hCut
  let q : ℝ := Kblock * Real.exp (-(hdepth : ℝ))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqSmall : q / b < η := by simpa [q] using hSieveError
  have hqLe : q ≤ b * η := by
    have hq' := (div_lt_iff₀ hb).mp hqSmall
    nlinarith [hq']
  have hbEta : b * η ≤ η := by
    calc
      b * η ≤ 1 * η := mul_le_mul_of_nonneg_right (le_of_lt hb_lt_one) hη.le
      _ = η := by ring
  have hqLtOne : q < 1 := by
    calc
      q ≤ b * η := hqLe
      _ ≤ η := hbEta
      _ ≤ 1 / 2 := hηhalf
      _ < 1 := by norm_num
  have hfactorNonneg : 0 ≤ 1 - q := by linarith
  have hfactorLe : 1 - q ≤ 1 := by linarith [hq0]
  have hqMain : q * (A / b) ≤ A * η := by
    calc
      q * (A / b) ≤ (b * η) * (A / b) :=
        mul_le_mul_of_nonneg_right hqLe (div_nonneg hA.le hb.le)
      _ = A * η := by
        field_simp [ne_of_gt hb]
        <;> ring
  have hfactorErr : (1 - q) * (ε / 4) ≤ ε / 4 := by
    calc
      (1 - q) * (ε / 4) ≤ 1 * (ε / 4) :=
        mul_le_mul_of_nonneg_right hfactorLe (by positivity)
      _ = ε / 4 := by ring
  have hCoeffBlock :
      A / b - A * η - ε / 2 ≤ (1 - q) * (A / b - ε / 4) - ε / 4 := by
    nlinarith [hqMain, hfactorErr]
  have hAη : A * η ≤ ε / 16 := by
    have hm := mul_le_mul_of_nonneg_left hηcap hA.le
    have hratio : A / (A + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < A + 1)).2
      nlinarith
    calc
      A * η ≤ A * (ε / (16 * (A + 1))) := hm
      _ = (ε / 16) * (A / (A + 1)) := by
        field_simp [ne_of_gt (by positivity : 0 < A + 1)]
        <;> ring
      _ ≤ (ε / 16) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = ε / 16 := by ring
  have hRoughScaled :
      singularSeries * roughDensity b 1 ≤ A / b + A * η := by
    calc
      singularSeries * roughDensity b 1 ≤
          singularSeries * (Real.exp (-Real.eulerMascheroniConstant) / b +
            Real.exp (-Real.eulerMascheroniConstant) * η) :=
        mul_le_mul_of_nonneg_left hRough hSing.le
      _ = A / b + A * η := by dsimp [A]; ring
  have hCoeff : singularSeries * roughDensity b 1 - ε ≤
      (1 - q) * (A / b - ε / 4) - ε / 4 := by
    have hErr : 2 * (A * η) + ε / 2 ≤ ε := by nlinarith [hAη]
    linarith [hRoughScaled, hCoeffBlock]
  have hMassEvent : ∀ᶠ x : ℝ in atTop, 0 ≤ C.mass x jstar := by
    have hB := hBound jstar hjstar
    filter_upwards [hB, eventually_ge_atTop (1 : ℝ)] with x hx h1
    rcases hx with ⟨hMassLower, _, _, _, _, _⟩
    have hx0 : 0 ≤ x := le_trans (by norm_num) h1
    have hLnonneg : 0 ≤ Analytic.L x := by
      simpa [Analytic.L] using Real.log_nonneg h1
    exact le_trans (mul_nonneg hx0 (Real.rpow_nonneg hLnonneg _)) hMassLower
  have hLogEvent : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.L x := by
    simpa [Analytic.L] using (Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hMassEvent, hLogEvent, hSieveEvent] with x hMass hLog hSift
  have hLpos : 0 < Analytic.L x := lt_of_lt_of_le zero_lt_one hLog
  have hRatio : 0 ≤ C.mass x jstar / Analytic.L x := div_nonneg hMass hLpos.le
  have hq' : Kblock * Real.exp (-(hdepth : ℝ)) ≤ 1 := by
    simpa [q] using hqLtOne.le
  have hSift' :
      ((1 - q) * (A / b - ε / 4) - ε / 4) * C.mass x jstar /
        Analytic.L x ≤ candidateSiftedMass C x jstar (x ^ b) := by
    simpa [q, A, hq'] using hSift
  calc
    (singularSeries * roughDensity b 1 - ε) * C.mass x jstar / Analytic.L x =
        (singularSeries * roughDensity b 1 - ε) *
          (C.mass x jstar / Analytic.L x) := by ring
    _ ≤ ((1 - q) * (A / b - ε / 4) - ε / 4) *
          (C.mass x jstar / Analytic.L x) :=
      mul_le_mul_of_nonneg_right hCoeff hRatio
    _ = ((1 - q) * (A / b - ε / 4) - ε / 4) * C.mass x jstar /
          Analytic.L x := by ring
    _ ≤ candidateSiftedMass C x jstar (x ^ b) := hSift'

end Erdos821.S10Sharp
