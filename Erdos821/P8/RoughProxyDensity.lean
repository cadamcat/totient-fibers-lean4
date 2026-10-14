import Erdos821.P8.PrimeDensity
import Erdos821.P8.DensityBounds
import Erdos821.P8.CofactorGeometry

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

/-- The rough-proxy component has exactly the requested complement-density supremum. -/
theorem rough_proxy_density_from_tasks (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (hcell : RoughCellDensityTask) :
    ∀ b kappa S gamma gamma' eps : ℝ, 0 < b → 0 < kappa → kappa < 1 / 50 →
      0 < S → b ≤ gamma → gamma < gamma' → gamma' ≤ 1 / 2 - kappa → 0 < eps →
      ∀ᶠ x : ℝ in atTop, ∀ m n u : ℕ,
        m * n = 2 * u + 1 → x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
        gamma < Real.log n / L x → Real.log n / L x ≤ gamma' →
        proxyConstant (.rough gamma) x S m ≤
          (sSup ((fun a : ℝ => roughDensity gamma (1 - a)) '' Set.Icc gamma gamma') + eps) /
            (L x * sieveProduct (W x)) := by
  intro b kappa S gamma gamma' eps hb hkappa _hkappaMax hS hbgamma horder hhi heps
  have hgamma : 0 < gamma := hb.trans_le hbgamma
  have hgap : gamma + gamma' < 1 := by linarith
  let M := sSup ((fun a : ℝ => roughDensity gamma (1 - a)) '' Set.Icc gamma gamma')
  have hM : 0 < M := densityComplement_sup_pos hgamma horder.le hgap
  let eta : ℝ := eps / (2 * (M + eps))
  have hMeta : 0 < M + eps := by linarith
  have heta : 0 < eta := div_pos heps (by positivity)
  have hetaHalf : eta < 1 / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (M + eps))).mpr
    linarith
  have hetaOne : 0 < 1 - eta := by linarith
  have hbudget : (1 - eta) * (M + eps) = M + eps / 2 := by
    dsimp [eta]
    field_simp
    ring
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_cofactor_geometry b kappa S gamma gamma' hb hkappa hS hbgamma horder hhi,
    eventually_proxyDenominator_sharp_lower hc hs hresidue b S eta hb hS heta,
    hcell hc b 2 kappa S hb (by norm_num) hkappa hS (eps / 4) (by linarith),
    eventually_density_complement_upper gamma gamma' (Real.log 5 + 1) (eps / 4)
      hgamma hgap (by linarith)] with x hx hgeometry hden hcount hcontinuous
  intro m n u hfactor hulo huhi haLo haHi
  rcases hgeometry m n u hfactor hulo huhi haLo haHi with ⟨hmlo, hmhi, hwgap, hwmax, hnear⟩
  have hL0 : 0 < L x := Real.log_pos hx
  have hY0 : 0 < logCellLower x S m := Real.exp_pos _
  have hdelta0 := cell_width_pos hx S
  have hV0 := sieveProduct_pos (W x)
  have hdenM := hden m hmlo hmhi
  have hD0 : 0 < (proxyDenominator x S m : ℝ) := lt_of_lt_of_le (by positivity) hdenM
  have hcontinuousM := hcontinuous (Real.log n / L x) (cellExponent x S m)
    ⟨haLo.le, haHi⟩ hnear
  change roughDensity gamma (cellExponent x S m) ≤ M + eps / 4 at hcontinuousM
  have hcountM := hcount gamma (cellExponent x S m) hbgamma hwgap hwmax
  rw [rpow_cellExponent hx S m] at hcountM
  have hupper : Real.exp (L x ^ (-S)) * logCellLower x S m = logCellUpper x S m := by
    rw [logCell_endpoint_relation]
    ring
  rw [hupper, ← logCell_eq_endpoints] at hcountM
  have hcoefficient : roughDensity gamma (cellExponent x S m) + eps / 4 ≤ M + eps / 2 := by
    linarith
  have hscaledCoefficient := mul_le_mul_of_nonneg_right hcoefficient
    (by positivity : 0 ≤ L x ^ (-S) * logCellLower x S m / L x)
  have hcountUpper : (((logCell x S m).filter (rough (x ^ gamma))).card : ℝ) ≤
      (M + eps / 2) * L x ^ (-S) * logCellLower x S m / L x := by
    apply hcountM.trans
    simpa only [mul_assoc, mul_div_assoc] using hscaledCoefficient
  have hnum : (∑ k ∈ logCell x S m, test (.rough gamma) x k) =
      (((logCell x S m).filter (rough (x ^ gamma))).card : ℝ) := by
    simp [test, Finset.sum_boole]
  change proxyConstant (.rough gamma) x S m ≤ (M + eps) / (L x * sieveProduct (W x))
  rw [proxyConstant, hnum]
  apply (div_le_div_iff₀ hD0 (by positivity : 0 < L x * sieveProduct (W x))).mpr
  have hscaledCount := mul_le_mul_of_nonneg_right hcountUpper
    (by positivity : 0 ≤ L x * sieveProduct (W x))
  have hcancel : ((M + eps / 2) * L x ^ (-S) * logCellLower x S m / L x) *
      (L x * sieveProduct (W x)) =
        (M + eps / 2) * L x ^ (-S) * logCellLower x S m * sieveProduct (W x) := by
    field_simp
  rw [hcancel] at hscaledCount
  calc
    _ ≤ (M + eps / 2) * L x ^ (-S) * logCellLower x S m * sieveProduct (W x) := hscaledCount
    _ = (M + eps) * ((1 - eta) * L x ^ (-S) * logCellLower x S m * sieveProduct (W x)) := by
      rw [show (M + eps / 2) = (M + eps) * (1 - eta) by rw [mul_comm]; exact hbudget.symm]
      ring
    _ ≤ (M + eps) * (proxyDenominator x S m : ℝ) :=
      mul_le_mul_of_nonneg_left hdenM hMeta.le

/-- Complete lead-side density assembly; the two assigned analytic count tasks remain explicit. -/
theorem proxyDensities_from_tasks (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (hcell : RoughCellDensityTask) : ProxyDensities :=
  ⟨prime_proxy_density_from_residue hc hs hresidue,
    rough_proxy_density_from_tasks hc hs hresidue hcell⟩

end Erdos821.P8Core

