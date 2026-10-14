import Erdos821.P6Off.Correlation
import Erdos821.P6Off.Dyadic

noncomputable section
open scoped BigOperators ContDiff
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

def dyadicHarmonicCutoff (t : ℝ) : ℂ := (t : ℂ) * (dyadicCutoff t : ℂ)

theorem dyadicHarmonicCutoff_contDiff : ContDiff ℝ ∞ dyadicHarmonicCutoff := by
  exact (Complex.ofRealCLM.contDiff).mul
    (Complex.ofRealCLM.contDiff.comp dyadicCutoff_contDiff)

theorem dyadicHarmonicCutoff_support :
    Function.support dyadicHarmonicCutoff ⊆ Set.Icc (1 / 2) 2 := by
  intro t ht
  apply dyadicCutoff_support
  intro hzero
  apply ht
  simp [dyadicHarmonicCutoff, hzero]

theorem dyadicHarmonicCutoff_derivative_bounds :
    ∃ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) ∧
      ∀ j y, ‖iteratedDeriv j dyadicHarmonicCutoff y‖ ≤ bounds j := by
  have hc : HasCompactSupport dyadicHarmonicCutoff :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc dyadicHarmonicCutoff_support
  have hb (j : ℕ) := hc.exists_bound_iteratedFDeriv dyadicHarmonicCutoff_contDiff j
  choose bounds hpos hb using hb
  exact ⟨bounds, hpos, fun j y => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hb j j le_rfl y⟩

theorem shiftEndpoint_bound (x U lo hi rho sigma xi C tau eta : ℝ) (c alpha : ℕ → ℂ)
    (r : ℕ) (hr : 0 < r) (chi : DirichletCharacter ℂ r)
    (htau : 0 < tau) (htaueta : tau < eta) (heta : eta < 1 / 4)
    (hcoef : ∀ n, ‖alpha n‖ ≤ L x ^ C ∧ ‖c n‖ ≤ L x ^ C)
    (hrough : ∀ n, alpha n ≠ 0 → rough (W x) n)
    (hrbound : (r : ℝ) ≤ L x ^ C) (hfreq0 : |rho + xi| ≤ L x ^ C)
    (hfreq1 : |sigma| ≤ L x ^ C)
    (hlo : x ^ tau ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ x ^ eta) :
    EndpointBound x C tau eta (shiftEndpoint U lo hi rho sigma xi c alpha r hr chi) := by
  refine ⟨htau, htaueta, heta, ?_, ?_, hrbound, hfreq0, ?_, hlo, hlohi, hhi⟩
  · intro n
    refine ⟨restricted_bound U _ alpha
      ((norm_nonneg (alpha 0)).trans (hcoef 0).1) (fun n => (hcoef n).1) n, ?_⟩
    simpa [shiftEndpoint] using (hcoef n).2
  · exact restricted_rough U (W x) alpha hrough
  · simpa [shiftEndpoint] using hfreq1

/-- Uniform ShiftEstimate application after the exact endpoint identification.
The dyadic cutoff and its derivative data are fixed before B. -/
theorem separated_correlation_bound (hshift : ShiftEstimate) (P : Geometry)
    (D C tau eta : ℝ) (hD : 0 < D) (hC : 0 < C) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (U lo hi rho sigma xi1 xi2 xi3 Z : ℝ)
        (c alpha : ℕ → ℂ) (r : ℕ) (hr : 0 < r)
        (character : DirichletCharacter ℂ r) (k : ℤ),
        Admissible P x G →
        EndpointBound x C tau eta (shiftEndpoint U lo hi rho sigma (-xi2) c alpha r hr character) →
        EndpointBound x C tau eta (shiftEndpoint U lo hi rho sigma xi1 c alpha r hr character) →
        k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
        x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
        0 < Z → |rho + xi3| ≤ L x ^ C → |rho| ≤ L x ^ C →
        (∀ m, alpha m ≠ 0 → GroupFree G m) → discrepancy x B (restricted U alpha) →
        ‖∑ z ∈ Finset.Icc ⌈(1 / 2 : ℝ) * Z⌉₊ ⌊2 * Z⌋₊,
          if 0 < z ∧ 0 < (z : ℤ) + k then
            (dyadicCutoff (z / Z) : ℂ) * mellin z xi3 *
              star (twistedHConvolution P G x U lo hi rho sigma (-xi2) c alpha r character z) *
              twistedHConvolution P G x U lo hi rho sigma xi1 c alpha r character ((z : ℤ) + k).toNat
          else 0‖ ≤ K * Z * L x ^ (-D) := by
  obtain ⟨bounds, hbounds, hderiv⟩ := dyadicHarmonicCutoff_derivative_bounds
  obtain ⟨B, K, hB, hK, hbound⟩ := hshift P D C tau eta (1 / 2) 2 bounds hD hC (by norm_num)
  refine ⟨B, K, hB, hK, ?_⟩
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hbound, hL.eventually (eventually_ge_atTop 1)] with x hbound hx
  intro G U lo hi rho sigma xi1 xi2 xi3 Z c alpha r hr character k hG hF hH hk hkbound hZlo hZhi hZ hfreq3 hrho hfree hdisc
  have hcut : CutoffBound x C (1 / 2) 2 dyadicHarmonicCutoff bounds := by
    refine ⟨dyadicHarmonicCutoff_contDiff, dyadicHarmonicCutoff_support, ?_⟩
    intro j y
    exact (hderiv j y).trans (by
      have hone : 1 ≤ L x ^ (C * (j + 1)) := Real.one_le_rpow hx (by positivity)
      simpa using mul_le_mul_of_nonneg_left hone (hbounds j))
  have hb := hbound G _ _ k Z (rho + xi3) (-rho) dyadicHarmonicCutoff hG hF hH hk hkbound
    hZlo hZhi hfreq3 (by simpa using hrho) hcut hdisc
  rw [separated_sum_eq_shiftCorrelation P G x U lo hi rho sigma xi1 xi2 xi3 Z (1 / 2) 2
    c alpha r hr character k (fun t => (dyadicCutoff t : ℂ)) hZ.ne' hfree]
  change ‖(Z : ℂ) * shiftCorrelation P G x Z (rho + xi3) (-rho) k _ _ dyadicHarmonicCutoff (1 / 2) 2‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  calc
    _ ≤ Z * (K * L x ^ (-D)) := mul_le_mul_of_nonneg_left hb hZ.le
    _ = _ := by ring


end Erdos821.P6Off
