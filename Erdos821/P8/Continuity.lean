import Erdos821.P8.DensityTasks

noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

private def piSumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n, ContinuousLinearMap.proj i

private lemma measure_pi_sum_level_zero (n : ℕ) (hn : 0 < n) (c : ℝ) :
    volume {t : Fin n → ℝ | ∑ i, t i = c} = 0 := by
  let i : Fin n := ⟨0, hn⟩
  let v : Fin n → ℝ := Pi.single i c
  let A : AffineSubspace ℝ (Fin n → ℝ) := AffineSubspace.mk' v (piSumCLM n).toLinearMap.ker
  have hsumv : piSumCLM n v = c := by
    simp [piSumCLM, v]
  have hsumv' : (piSumCLM n).toLinearMap v = c := hsumv
  have hset : (A : Set (Fin n → ℝ)) = {t | ∑ j, t j = c} := by
    ext t
    change (piSumCLM n).toLinearMap (t - v) = 0 ↔ ∑ j, t j = c
    rw [map_sub, hsumv', sub_eq_zero]
    simp [piSumCLM]
  have hnot : (Pi.single i (c + 1) : Fin n → ℝ) ∉ A := by
    change (Pi.single i (c + 1) : Fin n → ℝ) ∉ (A : Set (Fin n → ℝ))
    rw [hset]
    simp [i]
  have hne : A ≠ ⊤ := by
    intro htop
    exact hnot (htop ▸ Set.mem_univ _)
  rw [← hset]
  exact Measure.addHaar_affineSubspace volume A hne

private lemma measure_pi_coordinate_level_zero (n : ℕ) (i : Fin n) (c : ℝ) :
    volume {t : Fin n → ℝ | t i = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i c

private def densityIntegrand (gamma w : ℝ) (l : ℕ) (t : Fin (l - 1) → ℝ) : ℝ :=
  if (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma then
    (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹
  else 0

private lemma densityIntegrand_measurable (gamma w : ℝ) (l : ℕ) :
    Measurable (densityIntegrand gamma w l) := by
  unfold densityIntegrand
  have hcond : MeasurableSet {t : Fin (l - 1) → ℝ |
      (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma} := by
    measurability
  exact Measurable.ite hcond (by fun_prop) measurable_const

private lemma densityBoundary_ae (gamma w : ℝ) (l : ℕ) (hl : 2 ≤ l) :
    ∀ᵐ t : Fin (l - 1) → ℝ, (∀ i, t i ≠ gamma) ∧ (∑ i, t i) ≠ w - gamma := by
  have hn : 0 < l - 1 := by omega
  have hcoord : ∀ i : Fin (l - 1), ∀ᵐ t : Fin (l - 1) → ℝ, t i ≠ gamma := by
    intro i
    rw [ae_iff]
    simpa [not_ne_iff] using measure_pi_coordinate_level_zero (l - 1) i gamma
  have hsum : ∀ᵐ t : Fin (l - 1) → ℝ, (∑ i, t i) ≠ w - gamma := by
    rw [ae_iff]
    simpa [not_ne_iff] using measure_pi_sum_level_zero (l - 1) hn (w - gamma)
  filter_upwards [ae_all_iff.2 hcoord, hsum] with t ht hs
  exact ⟨ht, hs⟩

private lemma densityIntegrand_tendsto {gamma w : ℝ} {l : ℕ} {p : ℕ → ℝ × ℝ}
    {t : Fin (l - 1) → ℝ}
    (hgamma_pos : 0 < gamma)
    (hgamma : Tendsto (fun n => (p n).1) atTop (nhds gamma))
    (hw : Tendsto (fun n => (p n).2) atTop (nhds w))
    (hcoord : ∀ i, t i ≠ gamma) (hsum : (∑ i, t i) ≠ w - gamma) :
    Tendsto (fun n => densityIntegrand (p n).1 (p n).2 l t) atTop
      (nhds (densityIntegrand gamma w l t)) := by
  let P : ℕ → Prop := fun n =>
    (∀ i, (p n).1 ≤ t i) ∧ (∑ i, t i) ≤ (p n).2 - (p n).1
  let P₀ : Prop := (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma
  have hright : Tendsto (fun n => (p n).2 - (p n).1) atTop (nhds (w - gamma)) :=
    hw.sub hgamma
  have hcoord_stable : ∀ i, ∀ᶠ n in atTop, ((p n).1 ≤ t i) ↔ (gamma ≤ t i) := by
    intro i
    rcases lt_or_gt_of_ne (Ne.symm (hcoord i)) with hlt | hgt
    · filter_upwards [hgamma.eventually (Iio_mem_nhds hlt)] with n hn
      exact iff_of_true hn.le hlt.le
    · filter_upwards [hgamma.eventually (Ioi_mem_nhds hgt)] with n hn
      exact iff_of_false (not_le_of_gt hn) (not_le_of_gt hgt)
  have hcoords_stable : ∀ᶠ n in atTop, (∀ i, (p n).1 ≤ t i) ↔ (∀ i, gamma ≤ t i) := by
    filter_upwards [eventually_all.2 hcoord_stable] with n hn
    constructor
    · intro h i
      exact (hn i).mp (h i)
    · intro h i
      exact (hn i).mpr (h i)
  have hsum_stable : ∀ᶠ n in atTop,
      ((∑ i, t i) ≤ (p n).2 - (p n).1) ↔ ((∑ i, t i) ≤ w - gamma) := by
    rcases lt_or_gt_of_ne hsum with hlt | hgt
    · filter_upwards [hright.eventually (Ioi_mem_nhds hlt)] with n hn
      exact iff_of_true hn.le hlt.le
    · filter_upwards [hright.eventually (Iio_mem_nhds hgt)] with n hn
      exact iff_of_false (not_le_of_gt hn) (not_le_of_gt hgt)
  have hP_stable : ∀ᶠ n in atTop, P n ↔ P₀ := by
    filter_upwards [hcoords_stable, hsum_stable] with n hc hs
    change ((∀ i, (p n).1 ≤ t i) ∧ (∑ i, t i) ≤ (p n).2 - (p n).1) ↔
      ((∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma)
    exact and_congr hc hs
  by_cases hP₀ : P₀
  · have hP : ∀ᶠ n in atTop, P n := hP_stable.mono fun n hn => hn.mpr hP₀
    have hden : 0 < w - ∑ i, t i := by
      linarith [hP₀.2, hgamma_pos]
    have hden_tendsto : Tendsto (fun n => (p n).2 - ∑ i, t i) atTop
        (nhds (w - ∑ i, t i)) := by
      simpa using hw.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑ i, t i) atTop
        (nhds (∑ i, t i)))
    have hinv := hden_tendsto.inv₀ (ne_of_gt hden)
    have hformula : Tendsto
        (fun n => ((p n).2 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹) atTop
        (nhds ((w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹)) := by
      simpa using hinv.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => ∏ i, (t i)⁻¹) atTop (nhds (∏ i, (t i)⁻¹)))
    have heq : (fun n => densityIntegrand (p n).1 (p n).2 l t) =ᶠ[atTop]
        fun n => ((p n).2 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ := by
      filter_upwards [hP] with n hn
      simp [densityIntegrand, P, hn]
    have htarget : densityIntegrand gamma w l t =
        (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ := by
      simp [densityIntegrand, P₀, hP₀]
    rw [htarget]
    exact hformula.congr' heq.symm
  · have hnotP : ∀ᶠ n in atTop, ¬ P n :=
      hP_stable.mono fun n hn h => hP₀ (hn.mp h)
    have heq : (fun n => densityIntegrand (p n).1 (p n).2 l t) =ᶠ[atTop]
        fun _ => (0 : ℝ) := by
      filter_upwards [hnotP] with n hn
      simp [densityIntegrand, P, hn]
    have htarget : densityIntegrand gamma w l t = 0 := by
      simp [densityIntegrand, P₀, hP₀]
    rw [htarget]
    exact tendsto_const_nhds.congr' heq.symm

private lemma densityIntegrand_support_ball {gamma w : ℝ} {l : ℕ}
    {gamma' w' : ℝ} {t : Fin (l - 1) → ℝ}
    (hgamma : 0 < gamma) (hgamma' : gamma / 2 < gamma') (hw' : w' < w + 1)
    (hdom : (∀ i, gamma' ≤ t i) ∧ (∑ i, t i) ≤ w' - gamma') :
    t ∈ Metric.closedBall (0 : Fin (l - 1) → ℝ) (w + 1) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have hgamma'_pos : 0 < gamma' := by linarith
  have hsum_nonneg : 0 ≤ ∑ j, t j :=
    Finset.sum_nonneg fun j hj => (le_of_lt hgamma'_pos).trans (hdom.1 j)
  have hw'_pos : 0 < w' := by linarith [hdom.2]
  apply (pi_norm_le_iff_of_nonneg (by linarith)).2
  intro i
  have hti_pos : 0 < t i := lt_of_lt_of_le hgamma'_pos (hdom.1 i)
  have hsum_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin (l - 1))), 0 ≤ t j :=
    fun j _ => (le_of_lt hgamma'_pos).trans (hdom.1 j)
  have hti_sum : t i ≤ ∑ j, t j :=
    Finset.single_le_sum hsum_nonneg (Finset.mem_univ i)
  have hti_le : t i ≤ w + 1 := by linarith [hdom.2, hti_sum]
  rw [Real.norm_eq_abs, abs_of_nonneg hti_pos.le]
  exact hti_le

private lemma densityIntegrand_norm_bound {gamma : ℝ} {l : ℕ}
    {gamma' w' : ℝ} {t : Fin (l - 1) → ℝ} (hl : 2 ≤ l)
    (hgamma : 0 < gamma) (hgamma' : gamma / 2 < gamma')
    (hdom : (∀ i, gamma' ≤ t i) ∧ (∑ i, t i) ≤ w' - gamma') :
    ‖densityIntegrand gamma' w' l t‖ ≤ (gamma / 2)⁻¹ ^ l := by
  have hbase : 0 < gamma / 2 := by linarith
  have hbase_inv : (gamma / 2)⁻¹ = 2 / gamma := by
    field_simp [ne_of_gt hgamma]
  have hden : gamma / 2 ≤ w' - ∑ i, t i := by linarith [hdom.2]
  have hden_pos : 0 < w' - ∑ i, t i := hbase.trans_le hden
  have hden_inv : (w' - ∑ i, t i)⁻¹ ≤ 2 / gamma := by
    simpa [hbase_inv] using (one_div_le_one_div_of_le hbase hden)
  have hti_pos : ∀ i, 0 < t i := fun i => (by linarith [hgamma', hdom.1 i])
  have hti_inv : ∀ i, 0 ≤ (t i)⁻¹ ∧ (t i)⁻¹ ≤ 2 / gamma := by
    intro i
    constructor
    · exact inv_nonneg.mpr (le_of_lt (hti_pos i))
    · have hi : gamma / 2 ≤ t i := by linarith [hgamma', hdom.1 i]
      simpa [hbase_inv] using (one_div_le_one_div_of_le hbase hi)
  have hprod : (∏ i, (t i)⁻¹) ≤ (2 / gamma) ^ (l - 1) := by
    calc
      (∏ i, (t i)⁻¹) ≤ ∏ _i : Fin (l - 1), (2 / gamma) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (hti_inv i).1
        · intro i hi
          exact (hti_inv i).2
      _ = (2 / gamma) ^ (l - 1) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod_nonneg : 0 ≤ ∏ i, (t i)⁻¹ :=
    Finset.prod_nonneg fun i hi => (hti_inv i).1
  have hkernel_nonneg : 0 ≤ (w' - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hden_pos.le) hprod_nonneg
  rw [densityIntegrand, if_pos hdom, Real.norm_eq_abs, abs_of_nonneg hkernel_nonneg]
  calc
    (w' - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ ≤
    (2 / gamma) * (2 / gamma) ^ (l - 1) :=
      mul_le_mul hden_inv hprod hprod_nonneg (by positivity)
    _ = (2 / gamma) ^ l := by
      rw [show l = (l - 1) + 1 by omega, pow_succ']
      rw [show l - 1 + 1 - 1 = l - 1 by omega]
    _ = (gamma / 2)⁻¹ ^ l := by rw [hbase_inv]

private lemma densityTerm_tendsto {gamma w : ℝ} {l : ℕ} {p : ℕ → ℝ × ℝ}
    (hgamma_pos : 0 < gamma) (hl : 2 ≤ l)
    (hp : Tendsto p atTop (nhds (gamma, w))) :
    Tendsto (fun n => densityTerm (p n).1 (p n).2 l) atTop (nhds (densityTerm gamma w l)) := by
  have hgamma : Tendsto (fun n => (p n).1) atTop (nhds gamma) := by
    change Tendsto (Prod.fst ∘ p) atTop (nhds gamma)
    exact (continuous_fst.tendsto (gamma, w)).comp hp
  have hw : Tendsto (fun n => (p n).2) atTop (nhds w) := by
    change Tendsto (Prod.snd ∘ p) atTop (nhds w)
    exact (continuous_snd.tendsto (gamma, w)).comp hp
  let K : Set (Fin (l - 1) → ℝ) := Metric.closedBall 0 (w + 1)
  let C : ℝ := (2 / gamma) ^ l
  let bound : (Fin (l - 1) → ℝ) → ℝ := K.indicator (fun _ => C)
  have hbound_int : Integrable bound volume := by
    have hK : volume K ≠ ⊤ := (isCompact_closedBall (0 : Fin (l - 1) → ℝ) (w + 1)).measure_ne_top
    exact (integrableOn_const (μ := volume) (s := K) (C := C) hK).integrable_indicator
      (Metric.isClosed_closedBall.measurableSet)
  have hgamma_event : ∀ᶠ n in atTop, gamma / 2 < (p n).1 :=
    hgamma.eventually (Ioi_mem_nhds (by linarith))
  have hw_event : ∀ᶠ n in atTop, (p n).2 < w + 1 :=
    hw.eventually (Iio_mem_nhds (by linarith))
  have hparameter_event : ∀ᶠ n in atTop,
      gamma / 2 < (p n).1 ∧ (p n).2 < w + 1 := hgamma_event.and hw_event
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun t : Fin (l - 1) → ℝ => densityIntegrand (p n).1 (p n).2 l t) volume :=
    Filter.Eventually.of_forall fun n => (densityIntegrand_measurable _ _ _).aestronglyMeasurable
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t : Fin (l - 1) → ℝ, ‖densityIntegrand (p n).1 (p n).2 l t‖ ≤ bound t := by
    filter_upwards [hparameter_event] with n hn
    apply ae_of_all
    intro t
    by_cases hdom : (∀ i, (p n).1 ≤ t i) ∧ (∑ i, t i) ≤ (p n).2 - (p n).1
    · have htK : t ∈ K := densityIntegrand_support_ball hgamma_pos hn.1 hn.2 hdom
      simpa [bound, K, C, htK] using
        densityIntegrand_norm_bound hl hgamma_pos hn.1 hdom
    · by_cases htK : t ∈ K
      · simp [densityIntegrand, bound, K, C, hdom, htK]
        positivity
      · simp [densityIntegrand, bound, K, C, hdom, htK]
  have hlim : ∀ᵐ t : Fin (l - 1) → ℝ, Tendsto
      (fun n => densityIntegrand (p n).1 (p n).2 l t) atTop (nhds (densityIntegrand gamma w l t)) := by
    filter_upwards [densityBoundary_ae gamma w l hl] with t ht
    exact densityIntegrand_tendsto hgamma_pos hgamma hw ht.1 ht.2
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) bound hmeas hbound hbound_int hlim
  simpa [densityTerm, densityIntegrand] using hDCT

private lemma densityTerm_zero_of_lt {gamma w : ℝ} {l : ℕ}
    (hgamma : 0 < gamma) (hl : 2 ≤ l) (hsize : w < (l : ℝ) * gamma) :
    densityTerm gamma w l = 0 := by
  have hzero : ∀ t : Fin (l - 1) → ℝ, densityIntegrand gamma w l t = 0 := by
    intro t
    by_cases hdom : (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma
    · have hcastNat : l - 1 + 1 = l := Nat.sub_add_cancel (by omega : 1 ≤ l)
      have hcast : ((l - 1 : ℕ) : ℝ) + 1 = (l : ℝ) := by exact_mod_cast hcastNat
      have hlow : (l - 1 : ℝ) * gamma ≤ ∑ i, t i := by
        calc
          (l - 1 : ℝ) * gamma = ((l - 1 : ℕ) : ℝ) * gamma := by
            congr 1
            linarith [hcast]
          _ = ∑ _i : Fin (l - 1), gamma := by simp
          _ ≤ ∑ i, t i := Finset.sum_le_sum fun i hi => hdom.1 i
      have hcontra : (l : ℝ) * gamma ≤ w := by nlinarith [hdom.2, hlow, hcast]
      exact (False.elim ((not_lt_of_ge hcontra) hsize))
    · simp [densityIntegrand, hdom]
  change (∫ t : Fin (l - 1) → ℝ, densityIntegrand gamma w l t) = 0
  rw [show (fun t : Fin (l - 1) → ℝ => densityIntegrand gamma w l t) = fun _ => 0 from
    funext hzero]
  simp

/-- Any larger finite cutoff gives the same density; excess simplex terms vanish. -/
lemma roughDensity_eq_cutoff (gamma w : ℝ) (hgamma : 0 < gamma)
    (N : ℕ) (hcut : ⌊w / gamma⌋₊ ≤ N) :
    roughDensity gamma w = w⁻¹ +
      ∑ l ∈ Finset.Icc 2 N, densityTerm gamma w l / (l.factorial : ℝ) := by
  unfold roughDensity
  apply congrArg (fun x : ℝ => w⁻¹ + x)
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hcut)
  intro l hl hnot
  have hlower : 2 ≤ l := (Finset.mem_Icc.mp hl).1
  have hfloor_lt : ⌊w / gamma⌋₊ < l := by
    by_contra h
    have hmem : l ∈ Finset.Icc 2 ⌊w / gamma⌋₊ := Finset.mem_Icc.mpr ⟨hlower, le_of_not_gt h⟩
    exact hnot hmem
  have hratio : w / gamma < l := Nat.lt_of_floor_lt hfloor_lt
  have hsize : w < (l : ℝ) * gamma := (div_lt_iff₀ hgamma).mp hratio
  simp [densityTerm_zero_of_lt hgamma hlower hsize]

private lemma roughDensity_tendsto {gamma w : ℝ} {p : ℕ → ℝ × ℝ}
    (hgamma : 0 < gamma) (hw : gamma < w)
    (hseq : ∀ n, 0 < (p n).1 ∧ (p n).1 < (p n).2)
    (hp : Tendsto p atTop (nhds (gamma, w))) :
    Tendsto (fun n => roughDensity (p n).1 (p n).2) atTop
      (nhds (roughDensity gamma w)) := by
  have hgamma_tendsto : Tendsto (fun n => (p n).1) atTop (nhds gamma) := by
    change Tendsto (Prod.fst ∘ p) atTop (nhds gamma)
    exact (continuous_fst.tendsto (gamma, w)).comp hp
  have hw_tendsto : Tendsto (fun n => (p n).2) atTop (nhds w) := by
    change Tendsto (Prod.snd ∘ p) atTop (nhds w)
    exact (continuous_snd.tendsto (gamma, w)).comp hp
  have hratio_tendsto : Tendsto (fun n => (p n).2 / (p n).1) atTop (nhds (w / gamma)) :=
    hw_tendsto.div hgamma_tendsto (ne_of_gt hgamma)
  obtain ⟨N, hN⟩ := exists_nat_gt (w / gamma)
  let M : ℕ := max 2 N
  have hM2 : 2 ≤ M := by simp [M]
  have hMreal : w / gamma < (M : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast (Nat.le_max_right 2 N))
  have hratio_event : ∀ᶠ n in atTop, (p n).2 / (p n).1 < M :=
    hratio_tendsto.eventually (Iio_mem_nhds hMreal)
  have hsum_tendsto : Tendsto
      (fun n => ∑ l ∈ Finset.Icc 2 M,
        densityTerm (p n).1 (p n).2 l / (l.factorial : ℝ)) atTop
      (nhds (∑ l ∈ Finset.Icc 2 M, densityTerm gamma w l / (l.factorial : ℝ))) := by
    apply tendsto_finsetSum
    intro l hl
    have hl2 : 2 ≤ l := (Finset.mem_Icc.mp hl).1
    simpa [div_eq_mul_inv] using
      (densityTerm_tendsto hgamma hl2 hp).mul_const ((l.factorial : ℝ)⁻¹)
  have hwinv : Tendsto (fun n => ((p n).2)⁻¹) atTop (nhds (w⁻¹)) :=
    hw_tendsto.inv₀ (ne_of_gt (lt_trans hgamma hw))
  have hfinite : Tendsto
      (fun n => ((p n).2)⁻¹ + ∑ l ∈ Finset.Icc 2 M,
        densityTerm (p n).1 (p n).2 l / (l.factorial : ℝ)) atTop
      (nhds (w⁻¹ + ∑ l ∈ Finset.Icc 2 M,
        densityTerm gamma w l / (l.factorial : ℝ))) := hwinv.add hsum_tendsto
  have hevent_eq : (fun n => ((p n).2)⁻¹ + ∑ l ∈ Finset.Icc 2 M,
      densityTerm (p n).1 (p n).2 l / (l.factorial : ℝ)) =ᶠ[atTop]
      fun n => roughDensity (p n).1 (p n).2 := by
    filter_upwards [hratio_event] with n hn
    have hrpos : 0 < (p n).2 / (p n).1 :=
      div_pos (lt_trans (hseq n).1 (hseq n).2) (hseq n).1
    have hfloor : ⌊(p n).2 / (p n).1⌋₊ < M :=
      (Nat.floor_lt hrpos.le).2 hn
    exact (roughDensity_eq_cutoff (p n).1 (p n).2 (hseq n).1 M hfloor.le).symm
  have htarget_floor : ⌊w / gamma⌋₊ ≤ M := by
    have hrpos : 0 < w / gamma := div_pos (lt_trans hgamma hw) hgamma
    exact ((Nat.floor_lt hrpos.le).2 hMreal).le
  have htarget_eq := roughDensity_eq_cutoff gamma w hgamma M htarget_floor
  rw [htarget_eq]
  exact hfinite.congr' hevent_eq

theorem densityContinuityTask_proof : DensityContinuityTask := by
  rw [DensityContinuityTask, continuousOn_iff_continuous_domRestrict]
  apply (continuous_iff_seqContinuous).2
  intro p q hp
  change Tendsto (fun n => roughDensity (p n).val.1 (p n).val.2) atTop
    (nhds (roughDensity q.val.1 q.val.2))
  have hpval : Tendsto (fun n => (p n).val) atTop (nhds q.val) :=
    (continuous_subtype_val.tendsto q).comp hp
  exact roughDensity_tendsto q.property.1 q.property.2
    (fun n => (p n).property) hpval

example : DensityContinuityTask := densityContinuityTask_proof



end Erdos821.P8Core
