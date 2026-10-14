import Erdos821.P8.DensityBounds

noncomputable section
open scoped BigOperators

namespace Erdos821.P8Core
open Blueprint Filter

/-- The contribution of integers with at least two prime factors. -/
def densityRemainder (gamma w : ℝ) : ℝ := roughDensity gamma w - w⁻¹

lemma densityRemainder_nonneg {gamma w : ℝ} (hgamma : 0 ≤ gamma) :
    0 ≤ densityRemainder gamma w :=
  sub_nonneg.mpr (roughDensity_ge_inv hgamma)

/-- Every finite composite simplex sum is bounded by the full composite density. -/
lemma densityTerm_sum_le_remainder {gamma w : ℝ} (hgamma : 0 < gamma) (K : ℕ) :
    (∑ l ∈ Finset.Icc 2 K, densityTerm gamma w l / (l.factorial : ℝ)) ≤
      densityRemainder gamma w := by
  have hcut := roughDensity_eq_cutoff gamma w hgamma
    (max K ⌊w / gamma⌋₊) (Nat.le_max_right _ _)
  rw [densityRemainder, hcut, add_sub_cancel_left]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.le_max_left _ _))
    (fun l _ _ => div_nonneg (densityTerm_nonneg hgamma.le l) (Nat.cast_nonneg _))

lemma roughDensity_continuousAt {gamma w : ℝ} (hgamma : 0 < gamma)
    (hgw : gamma < w) :
    ContinuousAt (fun v : ℝ × ℝ => roughDensity v.1 v.2) (gamma, w) := by
  have hopen : IsOpen {v : ℝ × ℝ | 0 < v.1 ∧ v.1 < v.2} :=
    (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_snd)
  exact densityContinuityTask_proof.continuousAt (hopen.mem_nhds ⟨hgamma, hgw⟩)

lemma densityRemainder_continuousAt {gamma w : ℝ} (hgamma : 0 < gamma)
    (hgw : gamma < w) :
    ContinuousAt (fun v : ℝ × ℝ => densityRemainder v.1 v.2) (gamma, w) :=
  (roughDensity_continuousAt hgamma hgw).sub
    (continuous_snd.continuousAt.inv₀ (ne_of_gt (hgamma.trans hgw)))

private def densityCompactRegion (b wMax gap : ℝ) : Set (ℝ × ℝ) :=
  (Set.Icc b wMax ×ˢ Set.Icc b wMax) ∩ {v | v.1 + gap ≤ v.2}

private lemma densityCompactRegion_compact (b wMax gap : ℝ) :
    IsCompact (densityCompactRegion b wMax gap) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le (continuous_fst.add_const gap) continuous_snd)

private lemma mem_densityCompactRegion {b wMax gap gamma w : ℝ}
    (hgap : 0 < gap) (hbg : b ≤ gamma) (hgw : gamma + gap ≤ w) (hww : w ≤ wMax) :
    (gamma, w) ∈ densityCompactRegion b wMax gap := by
  exact ⟨⟨⟨hbg, by linarith⟩, ⟨by linarith, hww⟩⟩, hgw⟩

private lemma densityRemainder_region_continuous {b wMax gap : ℝ}
    (hb : 0 < b) (hgap : 0 < gap) :
    ContinuousOn (fun v : ℝ × ℝ => densityRemainder v.1 v.2)
      (densityCompactRegion b wMax gap) := by
  intro v hv
  have hsep : v.1 + gap ≤ v.2 := hv.2
  exact (densityRemainder_continuousAt (hb.trans_le hv.1.1.1)
    (by linarith : v.1 < v.2)).continuousWithinAt

/-- A single modulus controls both parameters, uniformly on every compact admissible region.
The perturbed point may lie outside the original region. -/
theorem densityRemainder_uniform_perturbation {b wMax gap eps : ℝ}
    (hb : 0 < b) (hgap : 0 < gap) (heps : 0 < eps) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ gamma w gamma' w' : ℝ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax →
      |gamma' - gamma| < rho → |w' - w| < rho →
      |densityRemainder gamma' w' - densityRemainder gamma w| < eps := by
  let K := densityCompactRegion b wMax gap
  let F : (ℝ × ℝ) → ℝ := fun v => densityRemainder v.1 v.2
  have hK : IsCompact K := densityCompactRegion_compact b wMax gap
  have hF : ∀ v ∈ K, ContinuousAt F v := by
    intro v hv
    have hsep : v.1 + gap ≤ v.2 := hv.2
    exact densityRemainder_continuousAt (hb.trans_le hv.1.1.1)
      (by linarith : v.1 < v.2)
  have hu := hK.uniformContinuousAt_of_continuousAt F hF
    (Metric.dist_mem_uniformity heps)
  obtain ⟨rho, hrho, hmod⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨rho, hrho, ?_⟩
  intro gamma w gamma' w' hbg hgw hww hg hw
  have hp : (gamma, w) ∈ K := mem_densityCompactRegion hgap hbg hgw hww
  have hdist : dist (gamma, w) (gamma', w') < rho := by
    simpa only [Prod.dist_eq, Real.dist_eq, abs_sub_comm, max_lt_iff] using And.intro hg hw
  have h := hmod hdist hp
  change dist (densityRemainder gamma w) (densityRemainder gamma' w') < eps at h
  simpa only [Real.dist_eq, abs_sub_comm] using h

/-- Small multiplicative losses and parameter inflations are absorbed uniformly.
This is the final continuity step in a finite-box upper approximation. -/
theorem densityRemainder_weighted_perturbation {b wMax gap eps : ℝ}
    (hb : 0 < b) (hgap : 0 < gap) (heps : 0 < eps) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ gamma w gamma' w' a : ℝ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax →
      |gamma' - gamma| < rho → |w' - w| < rho → 0 ≤ a → a < rho →
      (1 + a) * densityRemainder gamma' w' ≤ densityRemainder gamma w + eps := by
  let K := densityCompactRegion b wMax gap
  have hK := densityCompactRegion_compact b wMax gap
  obtain ⟨M, hM⟩ := hK.bddAbove_image (densityRemainder_region_continuous hb hgap)
  let H : ℝ := max 0 M + eps + 1
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨delta, hdelta, hmod⟩ := densityRemainder_uniform_perturbation
    (wMax := wMax) hb hgap (show 0 < eps / 2 by positivity)
  refine ⟨min delta (eps / (2 * H)), lt_min hdelta (by positivity), ?_⟩
  intro gamma w gamma' w' a hbg hgw hww hg hw ha harho
  have hnear := hmod gamma w gamma' w' hbg hgw hww
    (hg.trans_le (min_le_left _ _)) (hw.trans_le (min_le_left _ _))
  have hupper : densityRemainder gamma' w' < densityRemainder gamma w + eps / 2 :=
    by linarith [(abs_lt.mp hnear).2]
  have hbase : densityRemainder gamma w ≤ M :=
    hM (Set.mem_image_of_mem _ (mem_densityCompactRegion hgap hbg hgw hww))
  have hpert : densityRemainder gamma' w' ≤ H := by
    dsimp [H]
    linarith [le_max_right (0 : ℝ) M]
  have haH : a * H < eps / 2 := by
    have hsmall : a < eps / (2 * H) := harho.trans_le (min_le_right _ _)
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * H)).mp hsmall
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hpert ha
  nlinarith

/-- Uniform absorption of inflated finite simplex sums and their multiplicative box losses. -/
theorem densityTerm_sum_weighted_perturbation {b wMax gap eps : ℝ}
    (hb : 0 < b) (hgap : 0 < gap) (heps : 0 < eps) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ gamma w gamma' w' a : ℝ, ∀ K : ℕ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax →
      |gamma' - gamma| < rho → |w' - w| < rho → 0 ≤ a → a < rho →
      (1 + a) * (∑ l ∈ Finset.Icc 2 K,
        densityTerm gamma' w' l / (l.factorial : ℝ)) ≤
        roughDensity gamma w - w⁻¹ + eps := by
  obtain ⟨rho, hrho, hmod⟩ := densityRemainder_weighted_perturbation
    (wMax := wMax) hb hgap heps
  refine ⟨min rho (b / 2), lt_min hrho (by positivity), ?_⟩
  intro gamma w gamma' w' a K hbg hgw hww hg hw ha harho
  have hgamma' : 0 < gamma' := by
    have hdiff := (abs_lt.mp (hg.trans_le (min_le_right rho (b / 2)))).1
    linarith
  calc
    _ ≤ (1 + a) * densityRemainder gamma' w' :=
      mul_le_mul_of_nonneg_left (densityTerm_sum_le_remainder hgamma' K) (by linarith)
    _ ≤ densityRemainder gamma w + eps := hmod gamma w gamma' w' a hbg hgw hww
      (hg.trans_le (min_le_left _ _)) (hw.trans_le (min_le_left _ _)) ha
      (harho.trans_le (min_le_left _ _))

end Erdos821.P8Core

