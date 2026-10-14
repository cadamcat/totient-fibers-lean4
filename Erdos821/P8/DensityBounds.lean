import Erdos821.P8.Continuity

noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma densityTerm_nonneg {gamma w : ℝ} (hgamma : 0 ≤ gamma) (l : ℕ) :
    0 ≤ densityTerm gamma w l := by
  unfold densityTerm
  apply integral_nonneg
  intro t
  dsimp only
  split_ifs with ht
  · exact mul_nonneg (inv_nonneg.mpr (by linarith [ht.2]))
      (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (hgamma.trans (ht.1 i))))
  · exact le_rfl

lemma roughDensity_ge_inv {gamma w : ℝ} (hgamma : 0 ≤ gamma) :
    w⁻¹ ≤ roughDensity gamma w := by
  have hsum : 0 ≤ ∑ l ∈ Finset.Icc 2 ⌊w / gamma⌋₊,
      densityTerm gamma w l / (l.factorial : ℝ) :=
    Finset.sum_nonneg (fun l _ => div_nonneg (densityTerm_nonneg hgamma l) (Nat.cast_nonneg _))
  unfold roughDensity
  linarith

lemma roughDensity_pos {gamma w : ℝ} (hgamma : 0 < gamma) (hw : gamma < w) :
    0 < roughDensity gamma w :=
  (inv_pos.mpr (hgamma.trans hw)).trans_le (roughDensity_ge_inv hgamma.le)

lemma roughDensity_continuousOn {gamma lo hi : ℝ} (hgamma : 0 < gamma) (hlo : gamma < lo) :
    ContinuousOn (roughDensity gamma) (Set.Icc lo hi) := by
  have hc : ContinuousOn (fun v : ℝ × ℝ => roughDensity v.1 v.2)
      {v | 0 < v.1 ∧ v.1 < v.2} := densityContinuityTask_proof
  exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun w hw => ⟨hgamma, hlo.trans_le hw.1⟩)

lemma densityComplement_continuousOn {gamma gamma' : ℝ}
    (hgamma : 0 < gamma) (hgap : gamma + gamma' < 1) :
    ContinuousOn (fun a : ℝ => roughDensity gamma (1 - a)) (Set.Icc gamma gamma') := by
  apply (roughDensity_continuousOn (hi := 1 - gamma) hgamma
    (show gamma < 1 - gamma' by linarith)).comp
      (continuous_const.sub continuous_id).continuousOn
  intro a ha
  change 1 - gamma' ≤ 1 - a ∧ 1 - a ≤ 1 - gamma
  exact ⟨by linarith [ha.2], by linarith [ha.1]⟩

lemma densityComplement_bddAbove {gamma gamma' : ℝ}
    (hgamma : 0 < gamma) (hgap : gamma + gamma' < 1) :
    BddAbove ((fun a : ℝ => roughDensity gamma (1 - a)) '' Set.Icc gamma gamma') :=
  isCompact_Icc.bddAbove_image (densityComplement_continuousOn hgamma hgap)

lemma densityComplement_sup_pos {gamma gamma' : ℝ}
    (hgamma : 0 < gamma) (horder : gamma ≤ gamma') (hgap : gamma + gamma' < 1) :
    0 < sSup ((fun a : ℝ => roughDensity gamma (1 - a)) '' Set.Icc gamma gamma') := by
  have hvalue := le_csSup (densityComplement_bddAbove hgamma hgap)
    (Set.mem_image_of_mem (fun a : ℝ => roughDensity gamma (1 - a))
      (show gamma ∈ Set.Icc gamma gamma' from ⟨le_rfl, horder⟩))
  exact (roughDensity_pos hgamma (by linarith : gamma < 1 - gamma)).trans_le hvalue

/-- Compact continuity controls densities near the full complement interval. -/
theorem roughDensity_le_complement_sup_of_near {gamma gamma' eps : ℝ}
    (hgamma : 0 < gamma) (hgap : gamma + gamma' < 1) (heps : 0 < eps) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ a w : ℝ, a ∈ Set.Icc gamma gamma' →
      |w - (1 - a)| < rho →
      roughDensity gamma w ≤
        sSup ((fun a : ℝ => roughDensity gamma (1 - a)) '' Set.Icc gamma gamma') + eps := by
  let d : ℝ := (1 - gamma - gamma') / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let K : Set ℝ := Set.Icc (1 - gamma' - d) (1 - gamma + d)
  have hlo : gamma < 1 - gamma' - d := by dsimp [d]; linarith
  have hc : ContinuousOn (roughDensity gamma) K := roughDensity_continuousOn hgamma hlo
  have hu : UniformContinuousOn (roughDensity gamma) K :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc
  obtain ⟨rho, hrho, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu eps heps
  refine ⟨min d rho, lt_min hd hrho, ?_⟩
  intro a w ha hnear
  have hnearD := abs_lt.mp (hnear.trans_le (min_le_left d rho))
  have hnearRho := hnear.trans_le (min_le_right d rho)
  have hw : w ∈ K := ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have hbase : 1 - a ∈ K := ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have hdiff := hmod w hw (1 - a) hbase (by simpa only [Real.dist_eq] using hnearRho)
  have hdiff' : |roughDensity gamma w - roughDensity gamma (1 - a)| < eps := by
    simpa only [Real.dist_eq] using hdiff
  have hsup := le_csSup (densityComplement_bddAbove hgamma hgap)
    (Set.mem_image_of_mem (fun a : ℝ => roughDensity gamma (1 - a)) ha)
  linarith [(abs_lt.mp hdiff').2]

/-- A uniform O(1/log x) exponent perturbation is absorbed by any fixed density tolerance. -/
theorem eventually_density_complement_upper (gamma gamma' C eps : ℝ)
    (hgamma : 0 < gamma) (hgap : gamma + gamma' < 1) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ a w : ℝ, a ∈ Set.Icc gamma gamma' →
      |w - (1 - a)| ≤ C / L x →
      roughDensity gamma w ≤
        sSup ((fun a : ℝ => roughDensity gamma (1 - a)) '' Set.Icc gamma gamma') + eps := by
  obtain ⟨rho, hrho, hnear⟩ := roughDensity_le_complement_sup_of_near hgamma hgap heps
  have ht : Tendsto (fun x : ℝ => C / L x) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, L, Pi.inv_apply] using
      Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul C
  filter_upwards [ht.eventually (eventually_lt_nhds hrho)] with x hx
  intro a w ha hw
  exact hnear a w ha (hw.trans_lt hx)

end Erdos821.P8Core

