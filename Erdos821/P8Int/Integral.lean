import Erdos821.Blueprint.Proxy

noncomputable section
open scoped BigOperators ENNReal
open Filter MeasureTheory

namespace Erdos821.P8Int
open Blueprint Blueprint.Analytic

attribute [local instance] Classical.propDecidable

/-- Task: simplex partition by the minimum coordinate, with null ties. -/
def DensityIntegralTask : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 →
    (∫ a : ℝ in b..(1 / 2 : ℝ), roughDensity a (1 - a) / a) =
      roughDensity b 1 - 1

/-- The integrand of `densityTerm`, named for reuse. -/
def densIntegrand (γ w : ℝ) (l : ℕ) (t : Fin (l - 1) → ℝ) : ℝ :=
  if (∀ i, γ ≤ t i) ∧ (∑ i, t i) ≤ w - γ then
    (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹
  else 0

lemma densityTerm_eq (γ w : ℝ) (l : ℕ) :
    densityTerm γ w l = ∫ t : Fin (l - 1) → ℝ, densIntegrand γ w l t := rfl

lemma densIntegrand_nonneg {γ w : ℝ} (hγ : 0 ≤ γ) (l : ℕ) (t : Fin (l - 1) → ℝ) :
    0 ≤ densIntegrand γ w l t := by
  unfold densIntegrand
  split
  · next h =>
    obtain ⟨hge, hsum⟩ := h
    apply mul_nonneg
    · apply inv_nonneg.mpr
      linarith [hγ]
    · apply Finset.prod_nonneg
      intro i _
      apply inv_nonneg.mpr
      linarith [hge i, hγ]
  · exact le_refl 0

lemma densityTerm_nonneg {γ w : ℝ} (hγ : 0 ≤ γ) (l : ℕ) : 0 ≤ densityTerm γ w l := by
  rw [densityTerm_eq]
  apply integral_nonneg
  intro t
  exact densIntegrand_nonneg hγ l t

/-- Vanishing when the simplex is empty: `w < l * γ` forces the indicator to be false. -/
lemma densityTerm_eq_zero_of_lt {γ w : ℝ} (hγ : 0 ≤ γ) {l : ℕ} (h : w < l * γ) :
    densityTerm γ w l = 0 := by
  rw [densityTerm_eq]
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro t
  unfold densIntegrand
  split
  · next hcond =>
    obtain ⟨hge, hsum⟩ := hcond
    have hcard : ((Fintype.card (Fin (l - 1)) : ℕ) : ℝ) * γ ≤ ∑ i, t i := by
      have h1 : (∑ _i : Fin (l - 1), γ) ≤ ∑ i, t i :=
        Finset.sum_le_sum (fun i _ => hge i)
      rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have hl : (l : ℝ) * γ ≤ w := by
      cases l with
      | zero =>
        simp only [Nat.zero_sub, Fintype.card_fin, Nat.cast_zero, zero_mul] at hcard
        simp only [Nat.cast_zero, zero_mul] at h
        linarith [hsum]
      | succ n =>
        have hcardn : (n : ℝ) * γ ≤ ∑ i, t i := by
          have heq : Fintype.card (Fin (n + 1 - 1)) = n :=
            Fintype.card_fin _
          rw [heq] at hcard
          linarith
        have hcast : ((n + 1 : ℕ) : ℝ) * γ = (n : ℝ) * γ + γ := by
          push_cast
          ring
        linarith [hsum, hcast]
    linarith
  · rfl

/-- The `l = 1` term is `w⁻¹` on `0 ≤ w - γ`, else `0`. -/
lemma densityTerm_one (γ w : ℝ) :
    densityTerm γ w 1 = if 0 ≤ w - γ then w⁻¹ else 0 := by
  have h10 : (1 - 1 : ℕ) = 0 := rfl
  haveI : IsEmpty (Fin (1 - 1)) := h10.symm ▸ (inferInstance : IsEmpty (Fin 0))
  rw [densityTerm_eq]
  have hconst : ∀ t : Fin (1 - 1) → ℝ,
      densIntegrand γ w 1 t = (if 0 ≤ w - γ then w⁻¹ else 0) := by
    intro t
    unfold densIntegrand
    have hforall : (∀ i : Fin (1 - 1), γ ≤ t i) = True := by
      simp
    have hsum : (∑ _i : Fin (1 - 1), t _i) = 0 := Fintype.sum_empty _
    have hprod : (∏ _i : Fin (1 - 1), (t _i)⁻¹) = 1 := Fintype.prod_empty _
    simp only [hforall, hsum, hprod, true_and, sub_zero, mul_one]
  simp_rw [hconst]
  rw [integral_const]
  have hU : (volume : Measure (Fin (1 - 1) → ℝ)) Set.univ = 1 := by
    rw [volume_pi]
    exact Measure.pi_empty_univ _
  simp [Measure.real, hU]

/-- Joint measurability in `(a, t)` will give measurability in `a` of each term. -/
lemma measurable_densIntegrand_t (γ w : ℝ) (l : ℕ) :
    Measurable (densIntegrand γ w l) := by
  unfold densIntegrand
  apply Measurable.ite
  · -- The condition defines a measurable set.
    have h1 : MeasurableSet {t : Fin (l - 1) → ℝ | ∀ i, γ ≤ t i} := by
      have : {t : Fin (l - 1) → ℝ | ∀ i, γ ≤ t i} =
          ⋂ i, {t : Fin (l - 1) → ℝ | γ ≤ t i} := by
        ext t
        simp
      rw [this]
      apply MeasurableSet.iInter
      intro i
      exact (measurable_pi_apply i) measurableSet_Ici
    have h2 : MeasurableSet {t : Fin (l - 1) → ℝ | (∑ i, t i) ≤ w - γ} := by
      have hmeas : Measurable (fun t : Fin (l - 1) → ℝ => ∑ i, t i) :=
        Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      exact hmeas measurableSet_Iic
    have : {t : Fin (l - 1) → ℝ | (∀ i, γ ≤ t i) ∧ (∑ i, t i) ≤ w - γ} =
        {t | ∀ i, γ ≤ t i} ∩ {t | (∑ i, t i) ≤ w - γ} := rfl
    rw [this]
    exact h1.inter h2
  · -- The formula is measurable.
    have hsum : Measurable (fun t : Fin (l - 1) → ℝ => w - ∑ i, t i) :=
      measurable_const.sub (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
    have hprod : Measurable (fun t : Fin (l - 1) → ℝ => ∏ i, (t i)⁻¹) :=
      Finset.measurable_prod _ (fun i _ => (measurable_pi_apply i).inv)
    exact (hsum.inv.mul hprod)
  · exact measurable_const

lemma jointMeasurable_dens (l : ℕ) :
    Measurable (fun p : ℝ × (Fin (l - 1) → ℝ) =>
      densIntegrand p.1 (1 - p.1) l p.2) := by
  unfold densIntegrand
  apply Measurable.ite
  · have h1 : MeasurableSet {p : ℝ × (Fin (l - 1) → ℝ) | ∀ i, p.1 ≤ p.2 i} := by
      have : {p : ℝ × (Fin (l - 1) → ℝ) | ∀ i, p.1 ≤ p.2 i} =
          ⋂ i, {p : ℝ × (Fin (l - 1) → ℝ) | p.1 ≤ p.2 i} := by
        ext p
        simp
      rw [this]
      apply MeasurableSet.iInter
      intro i
      have hcont : Continuous (fun p : ℝ × (Fin (l - 1) → ℝ) => p.2 i - p.1) :=
        (continuous_apply i).comp continuous_snd |>.sub continuous_fst
      have hmeas : Measurable (fun p : ℝ × (Fin (l - 1) → ℝ) => p.2 i - p.1) :=
        hcont.measurable
      have : {p : ℝ × (Fin (l - 1) → ℝ) | p.1 ≤ p.2 i} =
          (fun p : ℝ × (Fin (l - 1) → ℝ) => p.2 i - p.1) ⁻¹' Set.Ici 0 := by
        ext p
        simp [sub_nonneg]
      rw [this]
      exact hmeas measurableSet_Ici
    have h2 : MeasurableSet {p : ℝ × (Fin (l - 1) → ℝ) | (∑ i, p.2 i) ≤ (1 - p.1) - p.1} := by
      have hcont : Continuous (fun p : ℝ × (Fin (l - 1) → ℝ) => (∑ i, p.2 i) + 2 * p.1) := by
        have hs : Continuous (fun p : ℝ × (Fin (l - 1) → ℝ) => ∑ i, p.2 i) :=
          continuous_finset_sum _ (fun i _ => (continuous_apply i).comp continuous_snd)
        exact hs.add (continuous_const.mul continuous_fst)
      have hmeas : Measurable (fun p : ℝ × (Fin (l - 1) → ℝ) => (∑ i, p.2 i) + 2 * p.1) :=
        hcont.measurable
      have : {p : ℝ × (Fin (l - 1) → ℝ) | (∑ i, p.2 i) ≤ (1 - p.1) - p.1} =
          (fun p : ℝ × (Fin (l - 1) → ℝ) => (∑ i, p.2 i) + 2 * p.1) ⁻¹' Set.Iic 1 := by
        ext p
        simp
        constructor
        · intro h
          linarith
        · intro h
          linarith
      rw [this]
      exact hmeas measurableSet_Iic
    have : {p : ℝ × (Fin (l - 1) → ℝ) | (∀ i, p.1 ≤ p.2 i) ∧ (∑ i, p.2 i) ≤ (1 - p.1) - p.1} =
        {p : ℝ × (Fin (l - 1) → ℝ) | ∀ i, p.1 ≤ p.2 i} ∩
        {p : ℝ × (Fin (l - 1) → ℝ) | (∑ i, p.2 i) ≤ (1 - p.1) - p.1} := rfl
    rw [this]
    exact h1.inter h2
  · have hsum : Measurable (fun p : ℝ × (Fin (l - 1) → ℝ) => (1 - p.1) - ∑ i, p.2 i) := by
      have hs : Measurable (fun p : ℝ × (Fin (l - 1) → ℝ) => ∑ i, p.2 i) :=
        Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp measurable_snd)
      -- `measurable_fst`, `measurable_snd` for product
      have hf : Measurable (fun p : ℝ × (Fin (l - 1) → ℝ) => (1 - p.1 : ℝ)) :=
        measurable_const.sub measurable_fst
      exact hf.sub hs
    -- NOTE: `measurable_fst/snd` may need explicit namespace; adjust if `lake env lean` fails.
    have hprod : Measurable (fun p : ℝ × (Fin (l - 1) → ℝ) => ∏ i, (p.2 i)⁻¹) :=
      Finset.measurable_prod _ (fun i _ => ((measurable_pi_apply i).comp measurable_snd).inv)
    exact (hsum.inv.mul hprod)
  · exact measurable_const

lemma stronglyMeasurable_density_in_a (l : ℕ) :
    StronglyMeasurable (fun a : ℝ => densityTerm a (1 - a) l) := by
  have hjoint : StronglyMeasurable
      (Function.uncurry (fun a : ℝ => fun t : Fin (l - 1) → ℝ => densIntegrand a (1 - a) l t)) :=
    (jointMeasurable_dens l).stronglyMeasurable
  have h := hjoint.integral_prod_right (ν := (volume : Measure (Fin (l - 1) → ℝ)))
  -- `h : StronglyMeasurable fun x => ∫ y, densIntegrand x (1-x) l y`, which is `densityTerm`.
  simpa [densityTerm_eq] using h

lemma continuousAt_inv_of_ne_zero {x : ℝ} (_hx : x ≠ 0) : True := trivial

/-- Pointwise bound on the simplex integrand when `a ∈ [b, 1/2]`. -/
lemma densIntegrand_le_pow (b a : ℝ) (hb : 0 < b) (hab : b ≤ a) (_ha2 : a ≤ 1 / 2)
    (l : ℕ) (hl : 1 ≤ l) (t : Fin (l - 1) → ℝ) :
    densIntegrand a (1 - a) l t ≤ (b⁻¹) ^ l := by
  unfold densIntegrand
  split
  · next hcond =>
    obtain ⟨hge, hsum⟩ := hcond
    have hb0 : (0 : ℝ) < b := hb
    have ha0 : 0 < a := lt_of_lt_of_le hb hab
    have h1 : ∀ i : Fin (l - 1), (t i)⁻¹ ≤ b⁻¹ := by
      intro i
      have hti : b ≤ t i := le_trans hab (hge i)
      have hpos : 0 < t i := lt_of_lt_of_le hb hti
      exact (inv_le_inv₀ hpos hb).mpr hti
    have h2 : ((1 - a) - ∑ i, t i)⁻¹ ≤ b⁻¹ := by
      have hge_sum : a ≤ (1 - a) - ∑ i, t i := by linarith [hsum]
      have hle : b ≤ (1 - a) - ∑ i, t i := le_trans hab hge_sum
      have hpos : 0 < (1 - a) - ∑ i, t i := lt_of_lt_of_le hb hle
      exact (inv_le_inv₀ hpos hb).mpr hle
    have h1nn : ∀ i ∈ (Finset.univ : Finset (Fin (l - 1))), 0 ≤ ((t i)⁻¹) := by
      intro i _
      have hti : 0 < t i := lt_of_lt_of_le hb (le_trans hab (hge i))
      exact (inv_pos.mpr hti).le
    have hprod_le : (∏ i, (t i)⁻¹) ≤ (b⁻¹) ^ (l - 1) := by
      have h1p : (∏ i : Fin (l - 1), (t i)⁻¹) ≤ ∏ _i : Fin (l - 1), b⁻¹ :=
        Finset.prod_le_prod₀ h1nn (fun i _ => h1 i)
      rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1p
    have h2nn : 0 ≤ ((1 - a) - ∑ i, t i)⁻¹ := by
      have hle : b ≤ (1 - a) - ∑ i, t i := le_trans hab (by linarith [hsum])
      exact (inv_pos.mpr (lt_of_lt_of_le hb hle)).le
    have hprod_nn : 0 ≤ (∏ i : Fin (l - 1), (t i)⁻¹) :=
      Finset.prod_nonneg (fun i hi => h1nn i hi)
    have hmul : ((1 - a) - ∑ i, t i)⁻¹ * (∏ i, (t i)⁻¹) ≤ b⁻¹ * (b⁻¹) ^ (l - 1) :=
      mul_le_mul h2 hprod_le hprod_nn (inv_pos.mpr hb).le
    have hl_eq : l = (l - 1) + 1 := (Nat.sub_add_cancel hl).symm
    have hpow : b⁻¹ * (b⁻¹) ^ (l - 1) = (b⁻¹) ^ l := by
      conv_rhs => rw [hl_eq, pow_succ]
      exact mul_comm _ _
    rwa [hpow] at hmul
  · -- Outside the simplex the integrand is `0 ≤ (b⁻¹)^l` since `b⁻¹ >0`.
    have hbpos : 0 < (b⁻¹) ^ l := pow_pos (inv_pos.mpr hb) l
    linarith [hbpos]

/-- Box containing the simplex support. -/
def simBox (b : ℝ) (l : ℕ) : Set (Fin (l - 1) → ℝ) :=
  Set.Icc (fun _ => b) (fun _ => 1)

lemma simBox_meas (b : ℝ) (l : ℕ) : MeasurableSet (simBox b l) :=
  measurableSet_Icc

lemma simBox_finite (b : ℝ) (l : ℕ) : (volume : Measure (Fin (l - 1) → ℝ)) (simBox b l) < ∞ := by
  unfold simBox
  rw [Real.volume_Icc_pi]
  apply ENNReal.prod_lt_top
  intro i _
  exact ENNReal.ofReal_lt_top

lemma dens_support_subset_box (b a : ℝ) (hb : 0 < b) (hab : b ≤ a) (ha2 : a ≤ 1 / 2)
    (l : ℕ) (t : Fin (l - 1) → ℝ) (ht : densIntegrand a (1 - a) l t ≠ 0) :
    t ∈ simBox b l := by
  have hcond : (∀ i, a ≤ t i) ∧ (∑ i, t i) ≤ (1 - a) - a := by
    by_contra hnc
    have h0 : densIntegrand a (1 - a) l t = 0 := by
      unfold densIntegrand
      rw [if_neg hnc]
    exact ht h0
  obtain ⟨hge, hsum⟩ := hcond
  have ha0 : 0 < a := lt_of_lt_of_le hb hab
  have hnn : ∀ i, 0 ≤ t i := fun i => (lt_of_lt_of_le hb (le_trans hab (hge i))).le
  have hS_le1 : (∑ i, t i) ≤ 1 := by
    have : (∑ i, t i) ≤ (1 - a) - a := hsum
    have ha_nn : 0 ≤ a := ha0.le
    linarith
  have hle1 : ∀ i, t i ≤ 1 := by
    intro i
    have hrest_nn : 0 ≤ ∑ j ∈ Finset.univ.erase i, t j :=
      Finset.sum_nonneg (fun j _ => hnn j)
    have hsplit : t i + ∑ j ∈ Finset.univ.erase i, t j = ∑ j, t j :=
      Finset.add_sum_erase _ _ (Finset.mem_univ i)
    have hti_le : t i ≤ ∑ j, t j := by
      rw [← hsplit]
      exact le_add_of_nonneg_right hrest_nn
    exact le_trans hti_le hS_le1
  unfold simBox
  simp only [Set.mem_Icc]
  constructor
  · intro i
    exact le_trans hab (hge i)
  · intro i
    exact hle1 i

lemma dens_le_pow_of_mem (b a : ℝ) (hb : 0 < b) (hab : b ≤ a) (ha2 : a ≤ 1 / 2)
    (l : ℕ) (hl : 1 ≤ l) (t : Fin (l - 1) → ℝ) :
    ‖densIntegrand a (1 - a) l t‖ ≤ (b⁻¹) ^ l := by
  have hnn : 0 ≤ densIntegrand a (1 - a) l t := by
    apply densIntegrand_nonneg
    exact (lt_of_lt_of_le hb hab).le
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact densIntegrand_le_pow b a hb hab ha2 l hl t

/-- Uniform bound on `[b, 1/2]` for each fixed `l`, used for integrability. -/
lemma bound_densityTerm_div (b : ℝ) (hb : 0 < b) (l : ℕ) :
    ∃ C : ℝ, ∀ a : ℝ, b ≤ a → a ≤ 1 / 2 →
      ‖densityTerm a (1 - a) l / (l.factorial : ℝ) / a‖ ≤ C := by
  cases l with
  | zero =>
    -- `l = 0` is definitionally `l = 1` for `densityTerm` (both `Fin 0`); bound by `2/b`.
    refine ⟨2 / b, ?_⟩
    intro a hab ha2
    have ha0 : 0 < a := lt_of_lt_of_le hb hab
    have h00 : densityTerm a (1 - a) 0 = densityTerm a (1 - a) 1 := rfl
    rw [h00, densityTerm_one]
    have hcond : 0 ≤ (1 - a) - a := by linarith
    rw [if_pos hcond]
    have h1a : (0:ℝ) < 1 - a := by linarith
    have hle1 : (1 - a)⁻¹ ≤ 2 := by
      have h12 : (1:ℝ)/2 ≤ 1 - a := by linarith
      have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2) h12
      simpa using this
    have hfact : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by simp
    rw [hfact]
    have hnn : 0 ≤ (1 - a)⁻¹ / 1 / a := by
      apply div_nonneg (div_nonneg (inv_pos.mpr h1a).le zero_le_one) ha0.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    simp only [div_one]
    have hle2 : a⁻¹ ≤ b⁻¹ := (inv_le_inv₀ ha0 hb).mpr hab
    have hmul : (1 - a)⁻¹ * a⁻¹ ≤ 2 * b⁻¹ :=
      mul_le_mul hle1 hle2 (inv_pos.mpr ha0).le (by norm_num)
    have heq1 : (1 - a)⁻¹ / a = (1 - a)⁻¹ * a⁻¹ := div_eq_mul_inv _ _
    have heq2 : (2:ℝ) / b = 2 * b⁻¹ := div_eq_mul_inv _ _
    rwa [heq1, heq2]
  | succ n =>
    -- `l = n+1 ≥ 1`: use pointwise bound plus box volume.
    have hl : 1 ≤ n + 1 := Nat.le_add_left 1 n
    have hfact_pos : (0:ℝ) < ((Nat.factorial (n+1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hvol_fin : (volume : Measure (Fin (n + 1 - 1) → ℝ)) (simBox b (n+1)) < ∞ :=
      simBox_finite b (n+1)
    have hvol_ne : (volume : Measure (Fin (n+1-1) → ℝ)) (simBox b (n+1)) ≠ ∞ :=
      ne_of_lt hvol_fin
    -- Volume as a real number.
    set V : ℝ := ((volume : Measure (Fin (n+1-1) → ℝ)) (simBox b (n+1))).toReal with hV
    have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
    set Cb : ℝ := (b⁻¹) ^ (n+1) * V / ((Nat.factorial (n+1) : ℕ) : ℝ) / b with hCb
    refine ⟨Cb, ?_⟩
    intro a hab ha2
    have ha0 : 0 < a := lt_of_lt_of_le hb hab
    -- Pointwise norm bound.
    have hpt : ∀ t : Fin (n+1-1) → ℝ, ‖densIntegrand a (1-a) (n+1) t‖ ≤ (b⁻¹)^(n+1) :=
      fun t => dens_le_pow_of_mem b a hb hab ha2 (n+1) hl t
    -- Support in box.
    have hsupp : ∀ t : Fin (n+1-1) → ℝ, t ∉ simBox b (n+1) →
        densIntegrand a (1-a) (n+1) t = 0 := by
      intro t ht
      by_contra hne
      exact ht (dens_support_subset_box b a hb hab ha2 (n+1) t hne)
    -- Rewrite integral as set integral over box.
    have h_eq : (∫ t : Fin (n+1-1) → ℝ, densIntegrand a (1-a) (n+1) t)
        = (∫ t in simBox b (n+1), densIntegrand a (1-a) (n+1) t) := by
      have h_ind : ∀ t : Fin (n+1-1) → ℝ,
          densIntegrand a (1-a) (n+1) t =
            (simBox b (n+1)).indicator (densIntegrand a (1-a) (n+1)) t := by
        intro t
        by_cases ht : t ∈ simBox b (n+1)
        · rw [Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht, hsupp t ht]
      rw [← integral_indicator (simBox_meas b (n+1))]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      exact h_ind t
    have hdt : densityTerm a (1-a) (n+1)
        = (∫ t in simBox b (n+1), densIntegrand a (1-a) (n+1) t) := by
      rw [densityTerm_eq]
      exact h_eq
    have hnorm_dt : ‖densityTerm a (1-a) (n+1)‖ ≤ (b⁻¹)^(n+1) * V := by
      rw [hdt]
      have hle := norm_setIntegral_le_of_norm_le_const hvol_fin (C := (b⁻¹)^(n+1))
        (fun x hx => hpt x)
      exact hle
    have hdt_nn : 0 ≤ densityTerm a (1-a) (n+1) :=
      densityTerm_nonneg (lt_of_lt_of_le hb hab).le _
    have hfact_nn : 0 ≤ ((Nat.factorial (n+1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hfact_pos : 0 < ((Nat.factorial (n+1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hCb_nn : 0 ≤ Cb := by
      unfold Cb
      apply div_nonneg (div_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr hb).le _) hVnn) hfact_nn) hb.le
    have hXnn : 0 ≤ densityTerm a (1-a) (n+1) / ((Nat.factorial (n+1) : ℕ) : ℝ) :=
      div_nonneg hdt_nn hfact_nn
    have hnorm_eq : ‖densityTerm a (1-a) (n+1) / ((Nat.factorial (n+1) : ℕ) : ℝ) / a‖
        = densityTerm a (1-a) (n+1) / ((Nat.factorial (n+1) : ℕ) : ℝ) / a := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg hXnn ha0.le
    rw [hnorm_eq]
    have hdt_val : densityTerm a (1-a) (n+1) ≤ (b⁻¹)^(n+1) * V := by
      have hnorm_eq_dt : ‖densityTerm a (1-a) (n+1)‖ = densityTerm a (1-a) (n+1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hdt_nn]
      rwa [hnorm_eq_dt] at hnorm_dt
    have hle1 : densityTerm a (1-a) (n+1) / ((Nat.factorial (n+1) : ℕ) : ℝ)
        ≤ (b⁻¹)^(n+1) * V / ((Nat.factorial (n+1) : ℕ) : ℝ) := by
      exact (div_le_div_iff_of_pos_right hfact_pos).mpr hdt_val
    have hYnn : 0 ≤ (b⁻¹)^(n+1) * V / ((Nat.factorial (n+1) : ℕ) : ℝ) :=
      div_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr hb).le _) hVnn) hfact_nn
    have hinv_le : a⁻¹ ≤ b⁻¹ := (inv_le_inv₀ ha0 hb).mpr hab
    have hinv_nn : 0 ≤ a⁻¹ := (inv_pos.mpr ha0).le
    have hmul_le : densityTerm a (1-a) (n+1) / ((Nat.factorial (n+1) : ℕ) : ℝ) * a⁻¹
        ≤ (b⁻¹)^(n+1) * V / ((Nat.factorial (n+1) : ℕ) : ℝ) * b⁻¹ :=
      mul_le_mul hle1 hinv_le hinv_nn hYnn
    have heq1 : densityTerm a (1-a) (n+1) / ((Nat.factorial (n+1) : ℕ) : ℝ) / a
        = densityTerm a (1-a) (n+1) / ((Nat.factorial (n+1) : ℕ) : ℝ) * a⁻¹ := by
      rw [div_eq_mul_inv]
    have heq2 : Cb = (b⁻¹)^(n+1) * V / ((Nat.factorial (n+1) : ℕ) : ℝ) * b⁻¹ := by
      unfold Cb
      rw [div_eq_mul_inv]
    rw [heq1, heq2]
    exact hmul_le

lemma densityTerm_zero_of_gt_half (a : ℝ) (ha : 1 / 2 < a) (l : ℕ) :
    densityTerm a (1 - a) l = 0 := by
  cases l with
  | zero =>
    have h10 : densityTerm a (1 - a) 0 = densityTerm a (1 - a) 1 := rfl
    rw [h10, densityTerm_one]
    have hneg : ¬ (0 ≤ (1 - a) - a) := by
      have : (1 - a) - a < 0 := by linarith
      linarith
    rw [if_neg hneg]
  | succ n =>
    apply densityTerm_eq_zero_of_lt (le_of_lt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) ha.le))
    -- Need `(1-a) < (n+1)*a`, i.e. `1 < (n+2)*a`.
    have ha0 : 0 < a := by linarith
    have h1 : (1:ℝ) < 2 * a := by linarith
    have h2 : (2:ℝ) ≤ ((n+1+1 : ℕ) : ℝ) := by
      have : 2 ≤ n+1+1 := by omega
      exact_mod_cast this
    have h3 : (2:ℝ) * a ≤ ((n+1+1 : ℕ) : ℝ) * a :=
      mul_le_mul_of_nonneg_right h2 ha0.le
    have h4 : (1:ℝ) < ((n+1+1 : ℕ) : ℝ) * a := lt_of_lt_of_le h1 h3
    have hcast : ((n + 1 + 1 : ℕ) : ℝ) = ((n+1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast, add_mul, one_mul] at h4
    have h5 : (1 - a) < ((n+1 : ℕ) : ℝ) * a := by linarith [h4]
    -- Goal is `(1-a) < ↑(n+1) * a`, which is `h5` (since `w=1-a`, `l*γ=(n+1)*a`).
    -- Need to rewrite `↑(n+1)` vs `↑(succ n)`? `n+1` vs `Nat.succ n` defeq? `cases` gives `succ n`, which is `n+1`? Actually `succ n = n+1`? Use `show`.
    simpa using h5

lemma intervalIntegrable_densityTerm_div (b : ℝ) (hb : 0 < b) (l : ℕ) :
    IntervalIntegrable (fun a : ℝ => densityTerm a (1 - a) l / (l.factorial : ℝ) / a)
      volume b (1 / 2 : ℝ) := by
  -- Strong measurability of the full integrand.
  have hSM : StronglyMeasurable
      (fun a : ℝ => densityTerm a (1 - a) l / (l.factorial : ℝ) / a) := by
    have h1 := stronglyMeasurable_density_in_a l
    have h2 : StronglyMeasurable (fun a : ℝ => ((l.factorial : ℕ) : ℝ)) :=
      stronglyMeasurable_const
    have h3 : StronglyMeasurable (fun a : ℝ => a) := stronglyMeasurable_id
    -- Combine via div (measurable operations preserve strong measurability for second-countable?).
    -- Use `Measurable` then convert: show `Measurable` first.
    have hmeas : Measurable (fun a : ℝ => densityTerm a (1 - a) l / (l.factorial : ℝ) / a) := by
      have hm1 : Measurable (fun a : ℝ => densityTerm a (1 - a) l) :=
        h1.measurable
      exact ((hm1.div measurable_const).div measurable_id)
    exact hmeas.stronglyMeasurable
  rw [IntervalIntegrable]
  constructor
  · -- `Ioc b (1/2)`: use bound when `b ≤ 1/2`, else empty.
    by_cases hb2 : b ≤ 1 / 2
    · have hfin : (volume : Measure ℝ) (Set.Ioc b (1/2)) ≠ ∞ := by
        have : (volume : Measure ℝ) (Set.Ioc b (1/2)) = ENNReal.ofReal (1/2 - b) := Real.volume_Ioc
        rw [this]
        exact ENNReal.ofReal_ne_top
      obtain ⟨C, hC⟩ := bound_densityTerm_div b hb l
      apply Measure.integrableOn_of_bounded hfin hSM.aestronglyMeasurable
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro a ha
      simp only [Set.mem_Ioc] at ha
      obtain ⟨hba, ha2⟩ := ha
      have hle := hC a hba.le ha2
      -- `hC` gives bound with `b ≤ a` (since `b < a` implies `b ≤ a`).
      exact hle
    · -- `b > 1/2`: `Ioc b (1/2) = ∅`.
      have hempty : Set.Ioc b (1/2 : ℝ) = ∅ := Set.Ioc_eq_empty (by linarith)
      rw [hempty]
      exact integrableOn_empty
  · -- `Ioc (1/2) b`: empty when `b ≤ 1/2`, else integrand vanishes (since `a > 1/2`).
    by_cases hb2 : b ≤ 1 / 2
    · have hempty : Set.Ioc (1/2 : ℝ) b = ∅ := Set.Ioc_eq_empty (by linarith)
      rw [hempty]
      exact integrableOn_empty
    · -- `1/2 < b`: show integrand is `0` on `Ioc (1/2) b`.
      have hfin : (volume : Measure ℝ) (Set.Ioc (1/2) b) ≠ ∞ := by
        have : (volume : Measure ℝ) (Set.Ioc (1/2) b) = ENNReal.ofReal (b - 1/2) := Real.volume_Ioc
        rw [this]
        exact ENNReal.ofReal_ne_top
      have hzero : ∀ a ∈ Set.Ioc (1/2 : ℝ) b,
          densityTerm a (1 - a) l / (l.factorial : ℝ) / a = 0 := by
        intro a ha
        simp only [Set.mem_Ioc] at ha
        obtain ⟨h12, _⟩ := ha
        rw [densityTerm_zero_of_gt_half a h12 l]
        simp
      -- Equals zero on the set, hence integrable.
      have hEqOn : Set.EqOn (fun a : ℝ => densityTerm a (1 - a) l / (l.factorial : ℝ) / a)
          0 (Set.Ioc (1/2) b) := hzero
      exact (integrableOn_congr_fun hEqOn measurableSet_Ioc).mpr integrableOn_zero

/-- Null tie where two independent coordinates agree. -/
lemma null_tie_indep (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (volume : Measure (Fin m → ℝ)) {t | t i = t j} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun t => t i - t j,
      map_add' := by
        intro x y
        simp only [Pi.add_apply]
        ring,
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, mul_sub, RingHom.id_apply] }
  have hL_def : ∀ t : Fin m → ℝ, L t = t i - t j := fun t => rfl
  have hL_ne : L ≠ 0 := by
    intro h0
    have ht : L (Pi.single i (1:ℝ)) = 1 := by
      rw [hL_def]
      simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
    rw [h0] at ht
    simp at ht
  have hker_ne : LinearMap.ker L ≠ ⊤ := by
    intro htop
    apply hL_ne
    exact LinearMap.ker_eq_top.mp htop
  have hvol : (volume : Measure (Fin m → ℝ)) ↑(LinearMap.ker L) = 0 :=
    Measure.addHaar_submodule _ _ hker_ne
  have hset_eq : {t : Fin m → ℝ | t i = t j} = ↑(LinearMap.ker L) := by
    ext t
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker]
    constructor
    · intro h
      have : L t = 0 := by
        rw [hL_def]
        exact sub_eq_zero.mpr h
      exact this
    · intro h
      have h2 : t i - t j = 0 := by
        have := h
        rwa [hL_def] at this
      exact sub_eq_zero.mp h2
  rwa [hset_eq]

/-- Null tie where an independent coordinate equals the dependent last coordinate
`1 - ∑`. Here `m = n+1` is the outer dimension, `t : Fin m → ℝ`. -/
lemma null_tie_dep (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    (volume : Measure (Fin m → ℝ)) {t | t i = 1 - ∑ j, t j} = 0 := by
  -- Linear map `L t = t i + ∑ t`, so tie is `L t = 1`.
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun t => t i + ∑ j, t j,
      map_add' := by
        intro x y
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        abel,
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply, smul_add] }
  have hL_def : ∀ t : Fin m → ℝ, L t = t i + ∑ j, t j := fun t => rfl
  have hL_ne : L ≠ 0 := by
    intro h0
    have ht : L (Function.update (0 : Fin m → ℝ) i 1) = 2 := by
      rw [hL_def]
      have hti : (Function.update (0 : Fin m → ℝ) i 1) i = 1 :=
        Function.update_self i 1 _
      have hsum : (∑ j : Fin m, Function.update (0 : Fin m → ℝ) i 1 j) = 1 := by
        have h1 : ∀ j : Fin m, j ≠ i → Function.update (0 : Fin m → ℝ) i 1 j = 0 := by
          intro j hj
          rw [Function.update_of_ne hj]
          rfl
        have h2 := Fintype.sum_eq_single i (fun j hj => h1 j hj)
        simpa [Function.update_self] using h2
      rw [hti, hsum]
      norm_num
    rw [h0] at ht
    simp [LinearMap.zero_apply] at ht
  have hker_ne : LinearMap.ker L ≠ ⊤ := by
    intro htop
    apply hL_ne
    exact LinearMap.ker_eq_top.mp htop
  -- Point `p₀` with `L p₀ = 1`: scale the witness with `L = 2` by `1/2`.
  set t₀ : Fin m → ℝ := Function.update (0 : Fin m → ℝ) i 1 with ht₀
  have ht₀L : L t₀ = 2 := by
    have ht : L (Function.update (0 : Fin m → ℝ) i 1) = 2 := by
      rw [hL_def]
      have hti : (Function.update (0 : Fin m → ℝ) i 1) i = 1 :=
        Function.update_self i 1 _
      have hsum : (∑ j : Fin m, Function.update (0 : Fin m → ℝ) i 1 j) = 1 := by
        have h1 : ∀ j : Fin m, j ≠ i → Function.update (0 : Fin m → ℝ) i 1 j = 0 := by
          intro j hj
          rw [Function.update_of_ne hj]
          rfl
        have h2 := Fintype.sum_eq_single i (fun j hj => h1 j hj)
        simpa [Function.update_self] using h2
      rw [hti, hsum]
      norm_num
    exact ht
  set p₀ : Fin m → ℝ := (1 / 2 : ℝ) • t₀ with hp₀
  have hp₀L : L p₀ = 1 := by
    rw [hp₀, map_smul]
    simp only [ht₀L, smul_eq_mul]
    norm_num
  set s_aff : AffineSubspace ℝ (Fin m → ℝ) :=
    AffineSubspace.mk' p₀ (LinearMap.ker L) with hs_aff
  have hs_dir : s_aff.direction = LinearMap.ker L := by
    rw [hs_aff]
    exact AffineSubspace.direction_mk' _ _
  have hs_ne : s_aff ≠ ⊤ := by
    intro htop
    apply hker_ne
    have : s_aff.direction = ⊤ := by
      rw [htop]
      simp
    rwa [hs_dir] at this
  have hvol : (volume : Measure (Fin m → ℝ)) ↑s_aff = 0 :=
    Measure.addHaar_affineSubspace _ _ hs_ne
  have hset_eq : {t : Fin m → ℝ | t i = 1 - ∑ j, t j} = ↑s_aff := by
    ext t
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro h
      -- `L t = 1` from tie.
      have hLt : L t = 1 := by
        rw [hL_def]
        linarith [h]
      rw [hs_aff, AffineSubspace.mem_mk']
      have hsub : L (t - p₀) = 0 := by
        rw [map_sub, hp₀L]
        linarith [hLt]
      exact LinearMap.mem_ker.mpr hsub
    · intro h
      -- From `t ∈ s_aff`, get `L t = 1`, then tie.
      rw [hs_aff, AffineSubspace.mem_mk'] at h
      have hsub : L (t - p₀) = 0 :=
        LinearMap.mem_ker.mp h
      have hLt : L t = 1 := by
        have hsub2 : L t - L p₀ = 0 := by
          have := hsub
          rwa [map_sub] at this
        rw [hp₀L] at hsub2
        linarith
      rw [hL_def] at hLt
      linarith [hLt]
  rwa [hset_eq]

/-- Permuting independent coordinates preserves the outer integral. -/
lemma perm_preserves_outer (b : ℝ) (n : ℕ) (e : Equiv.Perm (Fin (n+1))) :
    (∫ t : Fin (n+1) → ℝ, densIntegrand b 1 (n+2) t)
      = ∫ t : Fin (n+1) → ℝ, densIntegrand b 1 (n+2) (fun i => t (e i)) := by
  have hpoint : ∀ t : Fin (n+1) → ℝ,
      densIntegrand b 1 (n+2) (fun i => t (e i)) = densIntegrand b 1 (n+2) t := by
    intro t
    unfold densIntegrand
    -- Condition `∀i, b ≤ ...` preserved since `e` bijective.
    have hforall : (∀ i, b ≤ t (e i)) ↔ (∀ i, b ≤ t i) := by
      constructor
      · intro h j
        obtain ⟨i, rfl⟩ := e.surjective j
        exact h i
      · intro h i
        exact h (e i)
    -- Sum preserved.
    have hsum : (∑ i : Fin (n+1), t (e i)) = ∑ i, t i := Equiv.sum_comp e t
    -- Product preserved.
    have hprod : (∏ i : Fin (n+1), (t (e i))⁻¹) = ∏ i, (t i)⁻¹ := by
      simpa using Equiv.prod_comp e (fun i => (t i)⁻¹)
    show (if ((∀ i : Fin (n+1), b ≤ t (e i)) ∧ ∑ i : Fin (n+1), t (e i) ≤ 1 - b)
        then ((1 - ∑ i : Fin (n+1), t (e i))⁻¹ * ∏ i : Fin (n+1), (t (e i))⁻¹) else 0)
      = (if ((∀ i : Fin (n+1), b ≤ t i) ∧ ∑ i : Fin (n+1), t i ≤ 1 - b)
        then ((1 - ∑ i : Fin (n+1), t i)⁻¹ * ∏ i : Fin (n+1), (t i)⁻¹) else 0)
    simp only [hforall, hsum, hprod]
  have hfun : (fun t : Fin (n+1) → ℝ => densIntegrand b 1 (n+2) (fun i => t (e i)))
      = (fun t : Fin (n+1) → ℝ => densIntegrand b 1 (n+2) t) :=
    funext hpoint
  rw [hfun]

/-- Outer domain for fixed `b`, `n`: `t : Fin (n+1) → ℝ` with `b ≤ t` and sum constraint. -/
def outerD (b : ℝ) (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {t | (∀ i, b ≤ t i) ∧ ∑ i, t i ≤ 1 - b}

def outerLast (n : ℕ) (t : Fin (n+1) → ℝ) : ℝ := 1 - ∑ i, t i

def outerF (b : ℝ) (n : ℕ) (t : Fin (n+1) → ℝ) : ℝ :=
  densIntegrand b 1 (n+2) t

def piece0 (b : ℝ) (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {t ∈ outerD b n | (∀ i, t 0 ≤ t i) ∧ t 0 ≤ outerLast n t}

def pieceJ (b : ℝ) (n : ℕ) (j : Fin (n+1)) : Set (Fin (n+1) → ℝ) :=
  {t ∈ outerD b n | (∀ i, t j ≤ t i) ∧ t j ≤ outerLast n t}

def pieceLast (b : ℝ) (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {t ∈ outerD b n | ∀ i, outerLast n t ≤ t i}

/-- Outer pieces cover the outer domain (minimum always exists). -/
lemma cover_outer (b : ℝ) (n : ℕ) (t : Fin (n+1) → ℝ) (ht : t ∈ outerD b n) :
    (∃ j : Fin (n+1), t ∈ pieceJ b n j) ∨ t ∈ pieceLast b n := by
  -- Minimum among independents exists since `Fin (n+1)` nonempty (`0` exists as `n+1>0`).
  have hne : (Finset.univ : Finset (Fin (n+1))).Nonempty := by
    refine ⟨0, Finset.mem_univ _⟩
  obtain ⟨jstar, _, hjmin⟩ := Finset.exists_min_image Finset.univ t hne
  -- `hjmin : ∀ a ∈ univ, t jstar ≤ t a`, i.e. `t jstar` minimal among independents.
  have hjle : ∀ i : Fin (n+1), t jstar ≤ t i := fun i => hjmin i (Finset.mem_univ _)
  by_cases hle : t jstar ≤ outerLast n t
  · left
    exact ⟨jstar, ht, hjle, hle⟩
  · right
    push_neg at hle
    -- `t_last < t jstar ≤ all independents`, so last minimal (with `≤`? Actually `<` implies `≤`).
    have hlast_le : ∀ i : Fin (n+1), outerLast n t ≤ t i := by
      intro i
      have h1 : outerLast n t < t jstar := hle
      have h2 : t jstar ≤ t i := hjle i
      linarith
    exact ⟨ht, hlast_le⟩

/-- Finite union of all ties is null (using already-proved single-tie null lemmas). -/
lemma null_all_ties (n : ℕ) :
    (volume : Measure (Fin (n+1) → ℝ))
      ((⋃ (i : Fin (n+1)) (j : Fin (n+1)), if i ≠ j then {t : Fin (n+1) → ℝ | t i = t j} else ∅)
        ∪ ⋃ i : Fin (n+1), {t : Fin (n+1) → ℝ | t i = 1 - ∑ j, t j}) = 0 := by
  have h_indep : ∀ i j : Fin (n+1),
      (volume : Measure (Fin (n+1) → ℝ))
        (if i ≠ j then {t : Fin (n+1) → ℝ | t i = t j} else ∅) = 0 := by
    intro i j
    by_cases hij : i ≠ j
    · rw [if_pos hij]
      exact null_tie_indep _ i j hij
    · rw [if_neg hij]
      exact measure_empty
  have h_dep : ∀ i : Fin (n+1),
      (volume : Measure (Fin (n+1) → ℝ)) {t : Fin (n+1) → ℝ | t i = 1 - ∑ j, t j} = 0 := by
    intro i
    exact null_tie_dep _ (Nat.le_add_left 1 n) i
  have h_union_indep : (volume : Measure (Fin (n+1) → ℝ))
      (⋃ (i : Fin (n+1)) (j : Fin (n+1)), if i ≠ j then {t | t i = t j} else ∅) = 0 := by
    rw [measure_iUnion_null]
    intro i
    rw [measure_iUnion_null]
    intro j
    exact h_indep i j
  have h_union_dep : (volume : Measure (Fin (n+1) → ℝ))
      (⋃ i : Fin (n+1), {t : Fin (n+1) → ℝ | t i = 1 - ∑ j, t j}) = 0 := by
    rw [measure_iUnion_null]
    intro i
    exact h_dep i
  exact measure_union_null h_union_indep h_union_dep

/-- Outer pieces are measurable (closed conditions). -/
lemma outer_meas_sets (b : ℝ) (n : ℕ) :
    MeasurableSet (outerD b n) ∧ MeasurableSet (piece0 b n)
      ∧ (∀ j : Fin (n+1), MeasurableSet (pieceJ b n j))
      ∧ MeasurableSet (pieceLast b n) := by
  have hD : MeasurableSet (outerD b n) := by
    unfold outerD
    have h1 : MeasurableSet {t : Fin (n+1) → ℝ | ∀ i, b ≤ t i} := by
      have : {t : Fin (n+1) → ℝ | ∀ i, b ≤ t i} = ⋂ i, {t | b ≤ t i} := by
        ext t
        simp
      rw [this]
      apply MeasurableSet.iInter
      intro i
      exact (measurable_pi_apply i) measurableSet_Ici
    have h2 : MeasurableSet {t : Fin (n+1) → ℝ | (∑ i, t i) ≤ 1 - b} := by
      have hmeas : Measurable (fun t : Fin (n+1) → ℝ => ∑ i, t i) :=
        Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      exact hmeas measurableSet_Iic
    have : {t : Fin (n+1) → ℝ | (∀ i, b ≤ t i) ∧ ∑ i, t i ≤ 1 - b} =
        {t | ∀ i, b ≤ t i} ∩ {t | (∑ i, t i) ≤ 1 - b} := rfl
    rw [this]
    exact h1.inter h2
  have hJ : ∀ j : Fin (n+1), MeasurableSet (pieceJ b n j) := by
    intro j
    have h1 : MeasurableSet {t : Fin (n+1) → ℝ | ∀ i, t j ≤ t i} := by
      have : {t : Fin (n+1) → ℝ | ∀ i, t j ≤ t i} = ⋂ i, {t | t j ≤ t i} := by
        ext t
        simp
      rw [this]
      apply MeasurableSet.iInter
      intro i
      have hmeas : Measurable (fun t : Fin (n+1) → ℝ => t j - t i) :=
        (measurable_pi_apply j).sub (measurable_pi_apply i)
      have : {t : Fin (n+1) → ℝ | t j ≤ t i} = (fun t => t j - t i) ⁻¹' Set.Iic 0 := by
        ext t
        simp [sub_nonpos]
      rw [this]
      exact hmeas measurableSet_Iic
    have h2 : MeasurableSet {t : Fin (n+1) → ℝ | t j ≤ 1 - ∑ i, t i} := by
      have hmeas : Measurable (fun t : Fin (n+1) → ℝ => t j + ∑ i, t i) :=
        (measurable_pi_apply j).add (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
      have : {t : Fin (n+1) → ℝ | t j ≤ 1 - ∑ i, t i} = (fun t => t j + ∑ i, t i) ⁻¹' Set.Iic 1 := by
        ext t
        simp
        constructor
        · intro h
          linarith
        · intro h
          linarith
      rw [this]
      exact hmeas measurableSet_Iic
    have : pieceJ b n j = outerD b n ∩ {t | ∀ i, t j ≤ t i} ∩ {t | t j ≤ 1 - ∑ i, t i} := by
      ext t
      simp only [pieceJ, outerLast, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact (hD.inter h1).inter h2
  have h0 : MeasurableSet (piece0 b n) := hJ 0
  have hL : MeasurableSet (pieceLast b n) := by
    have h1 : MeasurableSet {t : Fin (n+1) → ℝ | ∀ i, 1 - ∑ j, t j ≤ t i} := by
      have : {t : Fin (n+1) → ℝ | ∀ i, 1 - ∑ j, t j ≤ t i} =
          ⋂ i, {t | 1 - ∑ j, t j ≤ t i} := by
        ext t
        simp
      rw [this]
      apply MeasurableSet.iInter
      intro i
      have hmeas : Measurable (fun t : Fin (n+1) → ℝ => (∑ j, t j) + t i) :=
        (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)).add (measurable_pi_apply i)
      have : {t : Fin (n+1) → ℝ | 1 - ∑ j, t j ≤ t i} =
          (fun t => (∑ j, t j) + t i) ⁻¹' Set.Ici 1 := by
        ext t
        simp
        constructor
        · intro h
          linarith
        · intro h
          linarith
      rw [this]
      exact hmeas measurableSet_Ici
    have : pieceLast b n = outerD b n ∩ {t | ∀ i, 1 - ∑ j, t j ≤ t i} := by
      ext t
      simp only [pieceLast, outerLast, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact hD.inter h1
  exact ⟨hD, h0, hJ, hL⟩

/-- Outer integrand is nonnegative when `0 ≤ b` (in particular for perL with `0<b`). -/
lemma outerF_nn (b : ℝ) (hb0 : 0 ≤ b) (n : ℕ) (t : Fin (n+1) → ℝ) :
    0 ≤ outerF b n t := by
  unfold outerF
  exact densIntegrand_nonneg hb0 _ _

/-- Outer integrand measurable (from general densIntegrand measurability, up to defeq). -/
lemma outerF_meas (b : ℝ) (n : ℕ) : Measurable (outerF b n) := by
  unfold outerF
  exact measurable_densIntegrand_t b 1 (n + 2)

/-- Pointwise invariance of the outer integrand under coordinate permutations
(same proof as `perm_preserves_outer`, factored for reuse in piece equalities). -/
lemma outerF_comp_perm (b : ℝ) (n : ℕ) (e : Equiv.Perm (Fin (n+1)))
    (t : Fin (n+1) → ℝ) :
    outerF b n (fun i => t (e i)) = outerF b n t := by
  unfold outerF
  have hforall : (∀ i, b ≤ t (e i)) ↔ (∀ i, b ≤ t i) := by
    constructor
    · intro h j
      obtain ⟨i, rfl⟩ := e.surjective j
      exact h i
    · intro h i
      exact h (e i)
  have hsum : (∑ i : Fin (n+1), t (e i)) = ∑ i, t i := Equiv.sum_comp e t
  have hprod : (∏ i : Fin (n+1), (t (e i))⁻¹) = ∏ i, (t i)⁻¹ := by
    simpa using Equiv.prod_comp e (fun i => (t i)⁻¹)
  show (if ((∀ i : Fin (n+1), b ≤ t (e i)) ∧ ∑ i : Fin (n+1), t (e i) ≤ 1 - b)
      then ((1 - ∑ i : Fin (n+1), t (e i))⁻¹ * ∏ i : Fin (n+1), (t (e i))⁻¹) else 0)
    = (if ((∀ i : Fin (n+1), b ≤ t i) ∧ ∑ i : Fin (n+1), t i ≤ 1 - b)
      then ((1 - ∑ i : Fin (n+1), t i)⁻¹ * ∏ i : Fin (n+1), (t i)⁻¹) else 0)
  simp only [hforall, hsum, hprod]

/-- The outer integrand vanishes off the outer domain. -/
lemma outerF_eq_zero_of_not_mem (b : ℝ) (n : ℕ) (t : Fin (n+1) → ℝ)
    (ht : t ∉ outerD b n) : outerF b n t = 0 := by
  unfold outerF densIntegrand
  split_ifs with hcond
  · exact (ht hcond).elim
  · rfl

/-- Outer pieces cover implies total lintegral equals sum of piece lintegrals up to null overlaps.
Overlaps are contained in the null tie union, and covering holds everywhere by `cover_outer`. -/
lemma total_eq_sum_pieces_lin (b : ℝ) (hb : 0 < b) (n : ℕ) :
    (∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal (outerF b n t) ∂volume)
      = (∑ j : Fin (n+1), ∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) t) ∂volume)
        + ∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((pieceLast b n).indicator (outerF b n) t) ∂volume := by
  set T : Set (Fin (n+1) → ℝ) :=
    ((⋃ (i : Fin (n+1)) (j : Fin (n+1)), if i ≠ j then {t : Fin (n+1) → ℝ | t i = t j} else ∅)
      ∪ ⋃ i : Fin (n+1), {t : Fin (n+1) → ℝ | t i = 1 - ∑ j, t j}) with hTdef
  have hTnull : (volume : Measure (Fin (n+1) → ℝ)) T = 0 := by
    rw [hTdef]; exact null_all_ties n
  have hae : ∀ᵐ t ∂(volume : Measure (Fin (n+1) → ℝ)), t ∉ T :=
    compl_mem_ae_iff.mpr hTnull
  have hmemJ : ∀ (j : Fin (n+1)) (t : Fin (n+1) → ℝ),
      t ∈ pieceJ b n j → t ∈ outerD b n ∧ (∀ i, t j ≤ t i) ∧ t j ≤ outerLast n t :=
    fun j t ht => ⟨ht.1, ht.2.1, ht.2.2⟩
  have hmemL : ∀ (t : Fin (n+1) → ℝ),
      t ∈ pieceLast b n → t ∈ outerD b n ∧ (∀ i, outerLast n t ≤ t i) :=
    fun t ht => ⟨ht.1, ht.2⟩
  -- Membership in a tie set from equalities.
  have htieJI : ∀ (t : Fin (n+1) → ℝ) (j k : Fin (n+1)), j ≠ k → t j = t k → t ∈ T := by
    intro t j k hjk heq
    rw [hTdef]
    exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨k, by
      rw [if_pos hjk]; exact heq⟩⟩)
  have htieJL : ∀ (t : Fin (n+1) → ℝ) (j : Fin (n+1)), t j = outerLast n t → t ∈ T := by
    intro t j heq
    rw [hTdef]
    refine Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, ?_⟩)
    show t j = 1 - ∑ i, t i
    simpa [outerLast] using heq
  -- Pointwise equality off T.
  have hpoint : ∀ t : Fin (n+1) → ℝ, t ∉ T →
      ENNReal.ofReal (outerF b n t)
        = (∑ j : Fin (n+1), ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) t))
          + ENNReal.ofReal ((pieceLast b n).indicator (outerF b n) t) := by
    intro t htT
    by_cases htD : t ∈ outerD b n
    · obtain ⟨j, hj⟩ | hL := cover_outer b n t htD
      · -- An independent piece holds; no other piece does (else a tie).
        have hnotJ : ∀ k : Fin (n+1), k ≠ j → t ∉ pieceJ b n k := by
          intro k hkj hkJ
          obtain ⟨-, hjle, -⟩ := hmemJ j t hj
          obtain ⟨-, hkle, -⟩ := hmemJ k t hkJ
          exact htT (htieJI t j k (Ne.symm hkj) (le_antisymm (hjle k) (hkle j)))
        have hnotL : t ∉ pieceLast b n := by
          intro hLa
          obtain ⟨-, hjle, hjlast⟩ := hmemJ j t hj
          obtain ⟨-, hLle⟩ := hmemL t hLa
          exact htT (htieJL t j (le_antisymm hjlast (hLle j)))
        have hsum : (∑ k : Fin (n+1), ENNReal.ofReal ((pieceJ b n k).indicator (outerF b n) t))
            = ENNReal.ofReal (outerF b n t) := by
          rw [Finset.sum_eq_single j]
          · rw [Set.indicator_of_mem hj]
          · intro k _ hkj
            rw [Set.indicator_of_notMem (hnotJ k hkj), ENNReal.ofReal_zero]
          · intro hcon
            exact absurd (Finset.mem_univ j) hcon
        rw [hsum, Set.indicator_of_notMem hnotL, ENNReal.ofReal_zero, add_zero]
      · -- The last piece holds; no independent piece does.
        have hnotJ : ∀ k : Fin (n+1), t ∉ pieceJ b n k := by
          intro k hkJ
          obtain ⟨-, hkle, hklast⟩ := hmemJ k t hkJ
          obtain ⟨-, hLle⟩ := hmemL t hL
          exact htT (htieJL t k (le_antisymm hklast (hLle k)))
        have hsum : (∑ k : Fin (n+1), ENNReal.ofReal ((pieceJ b n k).indicator (outerF b n) t)) = 0 := by
          rw [Finset.sum_eq_zero]
          intro k _
          rw [Set.indicator_of_notMem (hnotJ k), ENNReal.ofReal_zero]
        rw [hsum, Set.indicator_of_mem hL, zero_add]
    · -- Off the outer domain everything vanishes.
      have hF0 : outerF b n t = 0 := outerF_eq_zero_of_not_mem b n t htD
      have hJ0 : ∀ k : Fin (n+1),
          ENNReal.ofReal ((pieceJ b n k).indicator (outerF b n) t) = 0 := by
        intro k
        rw [Set.indicator_of_notMem (fun h => htD (hmemJ k t h).1), ENNReal.ofReal_zero]
      have hL0 : ENNReal.ofReal ((pieceLast b n).indicator (outerF b n) t) = 0 := by
        rw [Set.indicator_of_notMem (fun h => htD (hmemL t h).1), ENNReal.ofReal_zero]
      rw [hF0, ENNReal.ofReal_zero, Finset.sum_eq_zero (fun k _ => hJ0 k), hL0, add_zero]
  rw [lintegral_congr_ae (hae.mono fun t ht => hpoint t ht)]
  have hmeasJ : ∀ j : Fin (n+1),
      Measurable (fun t : Fin (n+1) → ℝ => ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) t)) :=
    fun j => (outerF_meas b n |>.indicator ((outer_meas_sets b n).2.2.1 j)).ennreal_ofReal
  have hmeasL : Measurable (fun t : Fin (n+1) → ℝ => ENNReal.ofReal ((pieceLast b n).indicator (outerF b n) t)) :=
    (outerF_meas b n |>.indicator (outer_meas_sets b n).2.2.2).ennreal_ofReal
  rw [lintegral_add_left (Finset.measurable_sum _ (fun j _ => hmeasJ j))]
  rw [lintegral_finsetSum _ (fun j _ => hmeasJ j)]

/-- All independent pieces have equal lintegrals (swap 0↔j via piCongrLeft, pointwise F symmetry). -/
lemma pieces_eq_indep_lin (b : ℝ) (hb : 0 < b) (n : ℕ) (j : Fin (n+1)) :
    (∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) t) ∂volume)
      = ∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume := by
  classical
  set e : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 j with he
  set φ : (Fin (n+1) → ℝ) ≃ᵐ (Fin (n+1) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (n+1) => ℝ) e.symm with hφdef
  have hmp : MeasurePreserving (⇑φ) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin (n+1) => ℝ) e.symm
  -- Coercion computes as precomposition with `e`.
  have hφeq : ∀ (t : Fin (n+1) → ℝ) (a : Fin (n+1)), ⇑φ t a = t (e a) := by
    intro t a
    have h := MeasurableEquiv.piCongrLeft_apply_apply (e.symm)
      (β := fun _ : Fin (n+1) => ℝ) t (e a)
    rwa [Equiv.symm_apply_apply] at h
  have hej : e j = 0 := by rw [he]; exact Equiv.swap_apply_right 0 j
  have he0 : e 0 = j := by rw [he]; exact Equiv.swap_apply_left 0 j
  have hF : ∀ t : Fin (n+1) → ℝ, outerF b n (⇑φ t) = outerF b n t := by
    intro t
    have hfun : (⇑φ t) = fun i => t (e i) := funext (fun a => hφeq t a)
    rw [hfun]
    exact outerF_comp_perm b n e t
  have hD : ∀ t : Fin (n+1) → ℝ, ⇑φ t ∈ outerD b n ↔ t ∈ outerD b n := by
    intro t
    simp only [outerD, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hall, hsumle⟩
      refine ⟨fun i => ?_, ?_⟩
      · obtain ⟨k, rfl⟩ := e.surjective i
        have h := hall k
        rwa [hφeq] at h
      · have hsum : ∑ i, ⇑φ t i = ∑ i, t i := by
          simp_rw [hφeq]
          exact Equiv.sum_comp e t
        rwa [hsum] at hsumle
    · rintro ⟨hall, hsumle⟩
      refine ⟨?_, ?_⟩
      · intro i
        rw [hφeq]
        exact hall (e i)
      · have hsum : ∑ i, ⇑φ t i = ∑ i, t i := by
          simp_rw [hφeq]
          exact Equiv.sum_comp e t
        rwa [hsum]
  have hlast : ∀ t : Fin (n+1) → ℝ, outerLast n (⇑φ t) = outerLast n t := by
    intro t
    simp only [outerLast]
    congr 1
    simp_rw [hφeq]
    exact Equiv.sum_comp e t
  -- `φ` maps `piece0` onto `pieceJ j`.
  have hmap : ∀ t : Fin (n+1) → ℝ, t ∈ piece0 b n ↔ ⇑φ t ∈ pieceJ b n j := by
    intro t
    have h1j : (⇑φ t) j = t 0 := by rw [hφeq t j, hej]
    simp only [piece0, pieceJ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨htD, hjle, hjlast⟩
      refine ⟨(hD t).mpr htD, fun i => ?_, ?_⟩
      · have h := hjle (e i)
        rwa [h1j, hφeq t i]
      · rwa [h1j, hlast]
    · rintro ⟨htD, hjle, hjlast⟩
      refine ⟨(hD t).mp htD, fun i => ?_, ?_⟩
      · obtain ⟨k, rfl⟩ := e.surjective i
        have h := hjle k
        rw [h1j, hφeq t k] at h
        exact h
      · have h1 : (⇑φ t) j = t 0 := by rw [hφeq t j, hej]
        rwa [h1, hlast] at hjlast
  -- Pointwise composition equality of the integrands.
  have hcomp : ∀ t : Fin (n+1) → ℝ,
      ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) (⇑φ t))
        = ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) := by
    intro t
    by_cases ht : t ∈ piece0 b n
    · rw [Set.indicator_of_mem ((hmap t).mp ht), Set.indicator_of_mem ht, hF t]
    · have h1 : ⇑φ t ∉ pieceJ b n j := fun hcon => ht ((hmap t).mpr hcon)
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem ht]
  have hmeas : Measurable (fun t : Fin (n+1) → ℝ =>
      ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) t)) :=
    (outerF_meas b n |>.indicator ((outer_meas_sets b n).2.2.1 j)).ennreal_ofReal
  have hbase : (∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) t) ∂volume)
      = ∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) (⇑φ t)) ∂volume :=
    (MeasurePreserving.lintegral_comp hmp hmeas).symm
  rw [hbase]
  exact lintegral_congr_ae (ae_of_all _ fun t => hcomp t)


/-- Components of the inverse split-off-zero equivalence. -/
lemma piFinSuccAbove0_symm_fst (n : ℕ) (α : ℝ) (u : Fin n → ℝ) :
    ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) 0 = α := by
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv_apply, Fin.cons_zero]

lemma piFinSuccAbove0_symm_succ (n : ℕ) (α : ℝ) (u : Fin n → ℝ) (j : Fin n) :
    ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) j.succ = u j := by
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv_apply, Fin.cons_succ]

/-- Sum splitting through the inverse equivalence. -/
lemma piFinSuccAbove0_symm_sum (n : ℕ) (α : ℝ) (u : Fin n → ℝ) :
    ∑ i : Fin (n+1), ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) i
      = α + ∑ j : Fin n, u j := by
  rw [Fin.sum_univ_succ]
  simp only [piFinSuccAbove0_symm_fst, piFinSuccAbove0_symm_succ]

/-- Transfer a pi-side lintegral to an explicit product via split-off-zero. -/
lemma transfer_lin_prod (n : ℕ) (G : (Fin (n+1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ t : Fin (n+1) → ℝ, G t ∂volume)
      = ∫⁻ p : ℝ × (Fin n → ℝ),
        G (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm p)
        ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) 0
  rw [volume_pi]
  have hsymm_meas : Measurable
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.measurable
  have hcomp := MeasurePreserving.lintegral_comp hmp (hG.comp hsymm_meas)
  have hself : (fun t : Fin (n+1) → ℝ => (G ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) t)) = G := by
    funext t
    show G _ = G t
    congr 1
    exact MeasurableEquiv.symm_apply_apply _ t
  rw [hself] at hcomp
  exact hcomp

/-- Transferred membership in the distinguished piece, in explicit `(α, u)` form. -/
lemma mem_piece0_transfer (b : ℝ) (n : ℕ) (α : ℝ) (u : Fin n → ℝ) :
    ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) ∈ piece0 b n ↔
      ((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
        ∧ (∀ k, α ≤ u k) ∧ α ≤ 1 - (α + ∑ j, u j) := by
  simp only [piece0, outerD, outerLast, Set.mem_setOf_eq,
    Fin.forall_fin_succ, Fin.sum_univ_succ,
    piFinSuccAbove0_symm_fst, piFinSuccAbove0_symm_succ, le_refl, true_and]

/-- Transferred membership in the last piece, in explicit `(α, u)` form. -/
lemma mem_pieceLast_transfer (b : ℝ) (n : ℕ) (α : ℝ) (u : Fin n → ℝ) :
    ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) ∈ pieceLast b n ↔
      ((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
        ∧ (∀ k, 1 - (α + ∑ j, u j) ≤ u k) ∧ 1 - (α + ∑ j, u j) ≤ α := by
  simp only [pieceLast, outerD, outerLast, Set.mem_setOf_eq,
    Fin.forall_fin_succ, Fin.sum_univ_succ,
    piFinSuccAbove0_symm_fst, piFinSuccAbove0_symm_succ, le_refl, true_and]
  tauto

/-- Integrability of the inner simplex integrand on `[b, 1/2]`. -/
lemma integrable_dens_of_mem (b α : ℝ) (hb : 0 < b) (hab : b ≤ α) (ha2 : α ≤ 1 / 2)
    (n : ℕ) : Integrable (densIntegrand α (1 - α) (n + 1)) volume := by
  classical
  have hmeas : Measurable (densIntegrand α (1 - α) (n + 1)) :=
    measurable_densIntegrand_t α (1 - α) (n + 1)
  have hl : 1 ≤ n + 1 := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hbound : ∀ t : Fin (n + 1 - 1) → ℝ,
      ‖densIntegrand α (1 - α) (n + 1) t‖ ≤ (b⁻¹) ^ (n + 1) :=
    fun t => dens_le_pow_of_mem b α hb hab ha2 (n + 1) hl t
  have hsupp : ∀ t : Fin (n + 1 - 1) → ℝ,
      densIntegrand α (1 - α) (n + 1) t ≠ 0 → t ∈ simBox b (n + 1) :=
    fun t ht => dens_support_subset_box b α hb hab ha2 (n + 1) t ht
  have hfin : (volume : Measure (Fin (n + 1 - 1) → ℝ)) (simBox b (n + 1)) < ∞ :=
    simBox_finite b (n + 1)
  have hfin_ne : (volume : Measure (Fin (n + 1 - 1) → ℝ)) (simBox b (n + 1)) ≠ ∞ :=
    ne_of_lt hfin
  have hmeasSet : MeasurableSet (simBox b (n + 1)) := simBox_meas b (n + 1)
  have hIntOn : IntegrableOn (densIntegrand α (1 - α) (n + 1))
      (simBox b (n + 1)) volume := by
    apply Measure.integrableOn_of_bounded hfin_ne hmeas.aestronglyMeasurable
    apply ae_of_all
    intro t
    exact hbound t
  have hEq : densIntegrand α (1 - α) (n + 1)
      = (simBox b (n + 1)).indicator (densIntegrand α (1 - α) (n + 1)) := by
    funext t
    by_cases ht : t ∈ simBox b (n + 1)
    · rw [Set.indicator_of_mem ht]
    · have h0 : densIntegrand α (1 - α) (n + 1) t = 0 := by
        by_contra hne
        exact ht (hsupp t hne)
      rw [Set.indicator_of_notMem ht, h0]
  rw [hEq]
  exact (integrable_indicator_iff hmeasSet).mpr hIntOn

/-- Transferred outer integrand value formula (RHS in simp-normal form). -/
lemma outerF_transfer_eq (b : ℝ) (n : ℕ) (α : ℝ) (u : Fin n → ℝ) :
    outerF b n (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u))
      = if ((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
        then ((1 - (α + ∑ j, u j))⁻¹ * (α⁻¹ * ∏ j, (u j)⁻¹)) else 0 := by
  unfold outerF
  show (if ((∀ i : Fin (n+1), b ≤ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) i)
      ∧ ∑ i : Fin (n+1), ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) i ≤ 1 - b)
    then ((1 - ∑ i : Fin (n+1), ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) i)⁻¹
      * ∏ i : Fin (n+1), (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u) i)⁻¹) else 0)
    = (if ((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
      then ((1 - (α + ∑ j, u j))⁻¹ * (α⁻¹ * ∏ j, (u j)⁻¹)) else 0)
  simp only [Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.prod_univ_succ,
    piFinSuccAbove0_symm_fst, piFinSuccAbove0_symm_succ]

/-- Outer integrand is bounded by `(b⁻¹)^(n+2)` everywhere (for `0 < b`). -/
lemma outerF_le_pow (b : ℝ) (hb : 0 < b) (n : ℕ) (t : Fin (n+1) → ℝ) :
    ‖outerF b n t‖ ≤ (b⁻¹) ^ (n + 2) := by
  have hEq : outerF b n t
      = ((densIntegrand b 1 (n + 2) : (Fin (n+2-1) → ℝ) → ℝ) t) := rfl
  rw [hEq]
  have hbound : ∀ s : Fin (n+2-1) → ℝ,
      ‖densIntegrand b 1 (n + 2) s‖ ≤ (b⁻¹) ^ (n + 2) := by
    intro s
    unfold densIntegrand
    split
    · next hcond =>
      obtain ⟨hge, hsum⟩ := hcond
      have h1 : ∀ i : Fin (n+2-1), (s i)⁻¹ ≤ b⁻¹ := by
        intro i
        have hti : b ≤ s i := hge i
        have hpos : 0 < s i := lt_of_lt_of_le hb hti
        exact (inv_le_inv₀ hpos hb).mpr hti
      have hlast_le : (1 - ∑ i : Fin (n+2-1), s i)⁻¹ ≤ b⁻¹ := by
        have hle : b ≤ 1 - ∑ i : Fin (n+2-1), s i := by linarith [hsum]
        have hpos : 0 < 1 - ∑ i : Fin (n+2-1), s i := lt_of_lt_of_le hb hle
        exact (inv_le_inv₀ hpos hb).mpr hle
      have h1nn : ∀ i ∈ (Finset.univ : Finset (Fin (n+2-1))), 0 ≤ ((s i)⁻¹) := by
        intro i _
        exact (inv_pos.mpr (lt_of_lt_of_le hb (hge i))).le
      have hcard : Fintype.card (Fin (n+2-1)) = n + 1 := by
        have : n + 2 - 1 = n + 1 := by omega
        rw [this]
        exact Fintype.card_fin _
      have hprod_le : (∏ i : Fin (n+2-1), (s i)⁻¹) ≤ (b⁻¹) ^ (n + 1) := by
        have h1p : (∏ i : Fin (n+2-1), (s i)⁻¹) ≤ ∏ _i : Fin (n+2-1), b⁻¹ :=
          Finset.prod_le_prod₀ h1nn (fun i _ => h1 i)
        rwa [Finset.prod_const, Finset.card_univ, hcard] at h1p
      have hlast_nn : 0 ≤ (1 - ∑ i : Fin (n+2-1), s i)⁻¹ :=
        (inv_pos.mpr (lt_of_lt_of_le hb (by linarith [hsum] : b ≤ 1 - ∑ i : Fin (n+2-1), s i))).le
      have hprod_nn : 0 ≤ (∏ i : Fin (n+2-1), (s i)⁻¹) :=
        Finset.prod_nonneg (fun i hi => h1nn i hi)
      have hmul : (1 - ∑ i : Fin (n+2-1), s i)⁻¹ * (∏ i : Fin (n+2-1), (s i)⁻¹)
          ≤ b⁻¹ * (b⁻¹) ^ (n + 1) :=
        mul_le_mul hlast_le hprod_le hprod_nn (inv_pos.mpr hb).le
      have hpow : b⁻¹ * (b⁻¹) ^ (n + 1) = (b⁻¹) ^ (n + 2) := by ring
      have hval_nn : 0 ≤ (1 - ∑ i : Fin (n+2-1), s i)⁻¹ * (∏ i : Fin (n+2-1), (s i)⁻¹) :=
        mul_nonneg hlast_nn hprod_nn
      rw [Real.norm_eq_abs, abs_of_nonneg hval_nn]
      rw [hpow] at hmul
      exact hmul
    · have hbpos : 0 < (b⁻¹) ^ (n + 2) := pow_pos (inv_pos.mpr hb) _
      simpa using hbpos.le
  exact hbound t

/-- Outer support lies in the box `[b, 1]^(n+1)`. -/
lemma outerF_support_subset_box (b : ℝ) (hb : 0 < b) (n : ℕ) (t : Fin (n+1) → ℝ)
    (ht : outerF b n t ≠ 0) : t ∈ simBox b (n + 2) := by
  have hcond : (∀ i : Fin (n+2-1), b ≤ t i) ∧ (∑ i : Fin (n+2-1), t i) ≤ 1 - b := by
    by_contra hnc
    have h0 : outerF b n t = 0 := by
      have hEq : outerF b n t
          = ((densIntegrand b 1 (n + 2) : (Fin (n+2-1) → ℝ) → ℝ) t) := rfl
      rw [hEq]
      unfold densIntegrand
      rw [if_neg hnc]
    exact ht h0
  obtain ⟨hge, hsum⟩ := hcond
  have hge' : ∀ i : Fin (n+1), b ≤ t i := fun i => hge i
  have hsum' : (∑ i : Fin (n+1), t i) ≤ 1 - b := hsum
  have hnn : ∀ i : Fin (n+1), 0 ≤ t i := fun i => (lt_of_lt_of_le hb (hge' i)).le
  have hS_le1 : (∑ i : Fin (n+1), t i) ≤ 1 := by linarith [hsum', hb.le]
  have hle1 : ∀ i : Fin (n+1), t i ≤ 1 := by
    intro i
    have hrest_nn : 0 ≤ ∑ j ∈ Finset.univ.erase i, t j :=
      Finset.sum_nonneg (fun j _ => hnn j)
    have hsplit : t i + ∑ j ∈ Finset.univ.erase i, t j = ∑ j, t j :=
      Finset.add_sum_erase _ _ (Finset.mem_univ i)
    have hti_le : t i ≤ ∑ j, t j := by
      rw [← hsplit]
      exact le_add_of_nonneg_right hrest_nn
    exact le_trans hti_le hS_le1
  -- `simBox b (n+2)` is `Icc b 1` in `Fin ((n+2)-1) = Fin (n+1)`.
  have hmem : t ∈ Set.Icc (fun _ => b) (fun _ => (1:ℝ)) := by
    simp only [Set.mem_Icc]
    exact ⟨hge', hle1⟩
  -- Convert `Fin (n+2-1)` to `Fin (n+1)` (definitionally `n+2-1 = n+1`).
  have hEq : simBox b (n + 2) = Set.Icc (fun _ : Fin (n+1) => b) (fun _ : Fin (n+1) => (1:ℝ)) := rfl
  rw [hEq]
  exact hmem
  -- Actually `simBox b (n+2)` unfolds to `Icc` in `Fin (n+2-1)`; need defeq `n+2-1 = n+1`.
  -- `rfl` above holds since `n+2-1` reduces to `n+1`.

/-- Outer integrand is integrable (bounded + box support). -/
lemma integrable_outerF (b : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) (n : ℕ) :
    Integrable (outerF b n) volume := by
  classical
  have hmeas : Measurable (outerF b n) := outerF_meas b n
  have hbound : ∀ t : Fin (n+1) → ℝ, ‖outerF b n t‖ ≤ (b⁻¹) ^ (n + 2) :=
    fun t => outerF_le_pow b hb n t
  have hsupp : ∀ t : Fin (n+1) → ℝ, outerF b n t ≠ 0 → t ∈ simBox b (n + 2) :=
    fun t ht => outerF_support_subset_box b hb n t ht
  have hfin : (volume : Measure (Fin (n+2-1) → ℝ)) (simBox b (n + 2)) < ∞ :=
    simBox_finite b (n + 2)
  have hfin_ne : (volume : Measure (Fin (n+2-1) → ℝ)) (simBox b (n + 2)) ≠ ∞ :=
    ne_of_lt hfin
  -- Transport finiteness/measurability along `n+2-1 = n+1` defeq.
  have hfin_ne' : (volume : Measure (Fin (n+1) → ℝ)) (simBox b (n + 2)) ≠ ∞ := hfin_ne
  have hmeasSet : MeasurableSet (simBox b (n + 2)) := simBox_meas b (n + 2)
  have hmeasSet' : MeasurableSet (simBox b (n + 2) : Set (Fin (n+1) → ℝ)) := hmeasSet
  have hIntOn : IntegrableOn (outerF b n) (simBox b (n + 2)) volume := by
    apply Measure.integrableOn_of_bounded hfin_ne' hmeas.aestronglyMeasurable
    apply ae_of_all
    intro t
    exact hbound t
  have hEq : outerF b n = (simBox b (n + 2)).indicator (outerF b n) := by
    funext t
    by_cases ht : t ∈ simBox b (n + 2)
    · rw [Set.indicator_of_mem ht]
    · have h0 : outerF b n t = 0 := by
        by_contra hne
        exact ht (hsupp t hne)
      rw [Set.indicator_of_notMem ht, h0]
  rw [hEq]
  exact (integrable_indicator_iff hmeasSet').mpr hIntOn

/-- Pointwise transfer for the distinguished piece: `indicator * F = α⁻¹ * dens` when `b ≤ α`. -/
lemma piece0_transfer_indicator_eq (b : ℝ) (n : ℕ) (α : ℝ) (u : Fin n → ℝ) :
    (piece0 b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u))
      = if b ≤ α then α⁻¹ * densIntegrand α (1 - α) (n + 1) u else 0 := by
  classical
  have hmem := mem_piece0_transfer b n α u
  have hF := outerF_transfer_eq b n α u
  -- Dens value formula.
  have hDensEq : densIntegrand α (1 - α) (n + 1) u
      = if ((∀ k, α ≤ u k) ∧ ∑ j, u j ≤ (1 - α) - α)
        then (((1 - α) - ∑ j, u j)⁻¹ * ∏ j, (u j)⁻¹) else 0 := rfl
  have hvalEq : (1 - (α + ∑ j, u j))⁻¹ * (α⁻¹ * ∏ j, (u j)⁻¹)
      = α⁻¹ * ((((1 - α) - ∑ j, u j)⁻¹ * ∏ j, (u j)⁻¹)) := by
    have hEq : (1:ℝ) - (α + ∑ j, u j) = (1 - α) - ∑ j, u j := by ring
    rw [hEq]
    ring
  have hCondEq : (((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
        ∧ (∀ k, α ≤ u k) ∧ α ≤ 1 - (α + ∑ j, u j))
      ↔ (b ≤ α ∧ ((∀ k, α ≤ u k) ∧ ∑ j, u j ≤ (1 - α) - α)) := by
    constructor
    · rintro ⟨⟨⟨hbα, hbu⟩, hsum⟩, hle, hlast⟩
      refine ⟨hbα, hle, ?_⟩
      have : α + ∑ j, u j ≤ 1 - α := by linarith [hlast]
      have hEq : (1 - α) - ∑ j, u j = 1 - (α + ∑ j, u j) := by ring
      linarith [this, hEq]
    · rintro ⟨hbα, hle, hsumle⟩
      have hbu : ∀ k, b ≤ u k := fun k => le_trans hbα (hle k)
      have hsum : α + ∑ j, u j ≤ 1 - b := by
        have h1 : α + ∑ j, u j ≤ 1 - α := by linarith [hsumle]
        have h2 : (1:ℝ) - α ≤ 1 - b := by linarith [hbα]
        linarith
      have hlast : α ≤ 1 - (α + ∑ j, u j) := by linarith [hsumle]
      exact ⟨⟨⟨hbα, hbu⟩, hsum⟩, hle, hlast⟩
  by_cases hbα : b ≤ α
  · rw [if_pos hbα]
    have hLHS : (piece0 b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u))
        = if (((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
          ∧ (∀ k, α ≤ u k) ∧ α ≤ 1 - (α + ∑ j, u j))
          then ((1 - (α + ∑ j, u j))⁻¹ * (α⁻¹ * ∏ j, (u j)⁻¹)) else 0 := by
      have hmem' : (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u)
          ∈ piece0 b n)
          ↔ (((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
            ∧ (∀ k, α ≤ u k) ∧ α ≤ 1 - (α + ∑ j, u j)) := hmem
      by_cases hm : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u)
          ∈ piece0 b n
      · rw [Set.indicator_of_mem hm, hF]
        have hmCond : (((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
            ∧ (∀ k, α ≤ u k) ∧ α ≤ 1 - (α + ∑ j, u j)) := hmem'.mp hm
        rw [if_pos hmCond.1, if_pos hmCond]
      · rw [Set.indicator_of_notMem hm]
        have hmCond : ¬ (((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
            ∧ (∀ k, α ≤ u k) ∧ α ≤ 1 - (α + ∑ j, u j)) :=
          fun hh => hm (hmem'.mpr hh)
        -- `hF` is `outerF = if D then value else 0`; with `¬(D∧M)`, indicator is 0.
        -- Need to show `if D then value else 0` with `¬(D∧M)`? Actually indicator already 0,
        -- so LHS 0, RHS if with `¬(D∧M)` is 0. Good.
        rw [if_neg hmCond]
    rw [hLHS]
    have hRHS : α⁻¹ * densIntegrand α (1 - α) (n + 1) u
        = if (b ≤ α ∧ ((∀ k, α ≤ u k) ∧ ∑ j, u j ≤ (1 - α) - α))
          then α⁻¹ * ((((1 - α) - ∑ j, u j)⁻¹ * ∏ j, (u j)⁻¹)) else 0 := by
      rw [hDensEq]
      by_cases hc : ((∀ k, α ≤ u k) ∧ ∑ j, u j ≤ (1 - α) - α)
      · rw [if_pos hc, if_pos ⟨hbα, hc⟩]
      · rw [if_neg hc, if_neg (fun hh => hc hh.2)]
        ring
    rw [hRHS]
    by_cases hc : (((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
        ∧ (∀ k, α ≤ u k) ∧ α ≤ 1 - (α + ∑ j, u j))
    · have hc' : (b ≤ α ∧ ((∀ k, α ≤ u k) ∧ ∑ j, u j ≤ (1 - α) - α)) :=
        hCondEq.mp hc
      rw [if_pos hc, if_pos hc', hvalEq]
    · have hc' : ¬ (b ≤ α ∧ ((∀ k, α ≤ u k) ∧ ∑ j, u j ≤ (1 - α) - α)) :=
        fun hh => hc (hCondEq.mpr hh)
      rw [if_neg hc, if_neg hc']
  · rw [if_neg hbα]
    have hm : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u)
        ∉ piece0 b n := by
      intro hmem'
      exact hbα ((hmem.mp hmem').1.1.1)
    rw [Set.indicator_of_notMem hm]

/-- Last piece equals distinguished piece via fiberwise reflection (u-outer Tonelli + 1D reflection). -/
lemma pieceLast_eq_piece0_lin (b : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) (n : ℕ) :
    (∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((pieceLast b n).indicator (outerF b n) t) ∂volume)
      = ∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume := by
  classical
  have hGL : Measurable (fun t : Fin (n+1) → ℝ =>
      ENNReal.ofReal ((pieceLast b n).indicator (outerF b n) t)) :=
    (outerF_meas b n |>.indicator ((outer_meas_sets b n).2.2.2)).ennreal_ofReal
  have hG0 : Measurable (fun t : Fin (n+1) → ℝ =>
      ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t)) :=
    (outerF_meas b n |>.indicator ((outer_meas_sets b n).2.1)).ennreal_ofReal
  have e0s_meas : Measurable
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.measurable
  have hJL : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      ENNReal.ofReal ((pieceLast b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm p))) :=
    hGL.comp e0s_meas
  have hJ0 : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm p))) :=
    hG0.comp e0s_meas
  rw [transfer_lin_prod _ _ hGL, transfer_lin_prod _ _ hG0,
    lintegral_prod_symm _ hJL.aemeasurable, lintegral_prod_symm _ hJ0.aemeasurable]
  apply lintegral_congr_ae
  apply ae_of_all
  intro u
  -- Sections in `α` are measurable.
  have hsecL : Measurable (fun α : ℝ => ENNReal.ofReal ((pieceLast b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u)))) :=
    hJL.comp (measurable_id.prodMk measurable_const)
  have hsec0 : Measurable (fun α : ℝ => ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u)))) :=
    hJ0.comp (measurable_id.prodMk measurable_const)
  -- 1D reflection in `α` about `(1 - S)/2` preserves volume.
  have hrmp : MeasurePreserving (fun α : ℝ => (1 - ∑ j, u j) - α) volume volume := by
    have heq : (fun α : ℝ => (1 - ∑ j, u j) - α)
        = (fun y : ℝ => (1 - ∑ j, u j) + y) ∘ Neg.neg := by
      funext α
      simp [sub_eq_add_neg]
    rw [heq]
    exact (measurePreserving_add_left volume _).comp (Measure.measurePreserving_neg volume)
  -- Pointwise fiber equality under reflection.
  have hfib : ∀ α : ℝ,
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
        ((1 - ∑ j, u j) - α, u) ∈ pieceLast b n)
        ↔ (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
          (α, u) ∈ piece0 b n) := by
    intro α
    rw [mem_pieceLast_transfer, mem_piece0_transfer]
    have hCC : (1:ℝ) - (((1 - ∑ j, u j) - α) + ∑ j, u j) = α := by ring
    have e1 : b ≤ (1 - ∑ j, u j) - α ↔ α + ∑ j, u j ≤ 1 - b := by
      constructor <;> intro h <;> linarith
    have e2 : ((1 - ∑ j, u j) - α) + ∑ j, u j ≤ 1 - b ↔ b ≤ α := by
      constructor <;> intro h <;> linarith
    have e3 : (∀ k, 1 - (((1 - ∑ j, u j) - α) + ∑ j, u j) ≤ u k) ↔ ∀ k, α ≤ u k := by
      constructor
      · intro h k
        have hkk := h k
        rw [hCC] at hkk
        exact hkk
      · intro h k
        rw [hCC]
        exact h k
    have e4 : (1 - (((1 - ∑ j, u j) - α) + ∑ j, u j)) ≤ (1 - ∑ j, u j) - α
        ↔ α ≤ 1 - (α + ∑ j, u j) := by
      have hEq : (1 - ∑ j, u j) - α = 1 - (α + ∑ j, u j) := by ring
      rw [hCC, hEq]
    simp only [e1, e2, e3, e4]
    tauto
  -- Outer integrand is symmetric under the reflection (domain + values).
  have hFeq : ∀ α : ℝ,
      outerF b n (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
        ((1 - ∑ j, u j) - α, u))
        = outerF b n (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
          (α, u)) := by
    intro α
    rw [outerF_transfer_eq, outerF_transfer_eq]
    have e1 : b ≤ (1 - ∑ j, u j) - α ↔ α + ∑ j, u j ≤ 1 - b := by
      constructor <;> intro h <;> linarith
    have e2 : ((1 - ∑ j, u j) - α) + ∑ j, u j ≤ 1 - b ↔ b ≤ α := by
      constructor <;> intro h <;> linarith
    have hCC : (1 : ℝ) - (((1 - ∑ j, u j) - α) + ∑ j, u j) = α := by ring
    have hSwap : (1 - ∑ j, u j) - α = 1 - (α + ∑ j, u j) := by ring
    have hVal : ((1 - (((1 - ∑ j, u j) - α) + ∑ j, u j))⁻¹ *
        (((1 - ∑ j, u j) - α)⁻¹ * ∏ j, (u j)⁻¹))
        = ((1 - (α + ∑ j, u j))⁻¹ * (α⁻¹ * ∏ j, (u j)⁻¹)) := by
      rw [hCC, hSwap]
      ring
    have hCond : (((b ≤ (1 - ∑ j, u j) - α ∧ ∀ k, b ≤ u k) ∧
        (1 - ∑ j, u j) - α + ∑ j, u j ≤ 1 - b) ↔
        ((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)) := by
      simp only [e1, e2]
      tauto
    by_cases h : ((b ≤ α ∧ ∀ k, b ≤ u k) ∧ α + ∑ j, u j ≤ 1 - b)
    · have h' : ((b ≤ (1 - ∑ j, u j) - α ∧ ∀ k, b ≤ u k) ∧
          (1 - ∑ j, u j) - α + ∑ j, u j ≤ 1 - b) := hCond.mpr h
      rw [if_pos h', if_pos h, hVal]
    · have h' : ¬ ((b ≤ (1 - ∑ j, u j) - α ∧ ∀ k, b ≤ u k) ∧
          (1 - ∑ j, u j) - α + ∑ j, u j ≤ 1 - b) :=
        fun hh => h (hCond.mp hh)
      rw [if_neg h', if_neg h]
  have hIndEq : ∀ α : ℝ,
      (pieceLast b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
          ((1 - ∑ j, u j) - α, u))
      = (piece0 b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
          (α, u)) := by
    intro α
    by_cases hmem : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
        (α, u) ∈ piece0 b n
    · have hmem' : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
          ((1 - ∑ j, u j) - α, u) ∈ pieceLast b n := (hfib α).mpr hmem
      rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem, hFeq α]
    · have hmem' : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
          ((1 - ∑ j, u j) - α, u) ∉ pieceLast b n :=
        fun hh => hmem ((hfib α).mp hh)
      rw [Set.indicator_of_notMem hmem', Set.indicator_of_notMem hmem]
  have hbase := hrmp.lintegral_comp hsecL
  have hcongr : (∫⁻ α : ℝ, ENNReal.ofReal ((pieceLast b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
          ((1 - ∑ j, u j) - α, u))) ∂volume)
      = ∫⁻ α : ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
          (α, u))) ∂volume :=
    lintegral_congr_ae (ae_of_all _ fun α => congrArg ENNReal.ofReal (hIndEq α))
  -- `hbase : ∫ Last = ∫ Last ∘ reflection`; compose with `hcongr`.
  exact hbase.symm.trans hcongr

/-- Pointwise vanishing of the inner integrand for `α > 1/2`. -/
lemma dens_zero_of_gt_half (α : ℝ) (ha : 1 / 2 < α) (n : ℕ) (u : Fin n → ℝ) :
    densIntegrand α (1 - α) (n + 1) u = 0 := by
  unfold densIntegrand
  rw [if_neg]
  intro hcond
  obtain ⟨hge, hsum⟩ := hcond
  -- `∑ ≥ 0` since each `u ≥ α > 0`.
  have hpos : ∀ k : Fin n, 0 < u k := by
    intro k
    have hα0 : (0:ℝ) < α := by linarith
    have hle : α ≤ u k := hge k
    exact lt_of_lt_of_le hα0 hle
  have hsum_nn : 0 ≤ ∑ j : Fin n, u j := Finset.sum_nonneg (fun j _ => (hpos j).le)
  have hsum' : (∑ j : Fin n, u j) ≤ 1 - α - α := hsum
  -- But `(1-α)-α < 0` when `α > 1/2`.
  have hneg : (1 - α) - α < 0 := by linarith
  linarith

/-- Inner lintegral is zero when `¬ (b ≤ α)` (all indicators vanish). -/
lemma inner_zero_of_not_le (b : ℝ) (n : ℕ) (α : ℝ) (h : ¬ b ≤ α) :
    (∫⁻ u : Fin n → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u))) ∂volume) = 0 := by
  have h0 : ∀ u : Fin n → ℝ, (piece0 b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u)) = 0 := by
    intro u
    rw [piece0_transfer_indicator_eq b n α u, if_neg h]
  simp_rw [h0, ENNReal.ofReal_zero]
  exact lintegral_zero

/-- Inner lintegral is zero when `α > 1/2` (dens vanishes). -/
lemma inner_zero_of_gt_half (b : ℝ) (_hb : 0 < b) (n : ℕ) (α : ℝ) (ha : 1 / 2 < α) :
    (∫⁻ u : Fin n → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u))) ∂volume) = 0 := by
  by_cases hle : b ≤ α
  · have h0 : ∀ u : Fin n → ℝ, (piece0 b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u)) = 0 := by
      intro u
      rw [piece0_transfer_indicator_eq b n α u, if_pos hle,
        dens_zero_of_gt_half α ha n u, mul_zero]
    simp_rw [h0, ENNReal.ofReal_zero]
    exact lintegral_zero
  · exact inner_zero_of_not_le b n α hle

/-- Inner lintegral equals the RHS integrand when `b ≤ α ≤ 1/2`. -/
lemma inner_eq_H_of_mem (b : ℝ) (hb : 0 < b) (n : ℕ) (α : ℝ) (hab : b ≤ α)
    (ha2 : α ≤ 1 / 2) :
    (∫⁻ u : Fin n → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u))) ∂volume)
      = ENNReal.ofReal (densityTerm α (1 - α) (n + 1) / ((n + 1).factorial : ℝ) / α
        * ((n + 1).factorial : ℝ)) := by
  classical
  have hα0 : 0 < α := lt_of_lt_of_le hb hab
  have hαnn : 0 ≤ α⁻¹ := (inv_pos.mpr hα0).le
  have hfact_pos : (0:ℝ) < ((n + 1).factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos _
  -- Rewrite LHS via transfer.
  have hpoint : ∀ u : Fin n → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u)))
      = ENNReal.ofReal (α⁻¹) * ENNReal.ofReal (densIntegrand α (1 - α) (n + 1) u) := by
    intro u
    rw [piece0_transfer_indicator_eq b n α u, if_pos hab,
      ENNReal.ofReal_mul hαnn]
  have hmeas_dens : Measurable (fun u : Fin n → ℝ =>
      ENNReal.ofReal (densIntegrand α (1 - α) (n + 1) u)) := by
    have h : Measurable (densIntegrand α (1 - α) (n + 1)) :=
      measurable_densIntegrand_t α (1 - α) (n + 1)
    exact h.ennreal_ofReal
  have hLHS : (∫⁻ u : Fin n → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u))) ∂volume)
      = ENNReal.ofReal (α⁻¹) * ∫⁻ u : Fin n → ℝ,
        ENNReal.ofReal (densIntegrand α (1 - α) (n + 1) u) ∂volume := by
    rw [lintegral_congr_ae (ae_of_all _ fun u => hpoint u)]
    rw [lintegral_const_mul _ hmeas_dens]
  rw [hLHS]
  have hInt_n : Integrable (fun u : Fin n → ℝ => densIntegrand α (1 - α) (n + 1) u) volume :=
    integrable_dens_of_mem b α hb hab ha2 n
  have hnn_n : 0 ≤ᵐ[volume] (fun u : Fin n → ℝ => densIntegrand α (1 - α) (n + 1) u) :=
    Filter.Eventually.of_forall (fun u => densIntegrand_nonneg hα0.le (n + 1) u)
  have hofReal_n : ENNReal.ofReal (∫ u : Fin n → ℝ, densIntegrand α (1 - α) (n + 1) u ∂volume)
      = ∫⁻ u : Fin n → ℝ, ENNReal.ofReal (densIntegrand α (1 - α) (n + 1) u) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hInt_n hnn_n
  have hDT_n : densityTerm α (1 - α) (n + 1)
      = ∫ u : Fin n → ℝ, densIntegrand α (1 - α) (n + 1) u ∂volume := rfl
  rw [← hofReal_n, ← hDT_n]
  -- Now goal: `ofReal α⁻¹ * ofReal (densityTerm) = ofReal (densityTerm/fact/α*fact)`.
  have hEqReal : α⁻¹ * densityTerm α (1 - α) (n + 1)
      = densityTerm α (1 - α) (n + 1) / ((n + 1).factorial : ℝ) / α
        * ((n + 1).factorial : ℝ) := by
    have hfact_ne : ((n + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hαne : α ≠ 0 := ne_of_gt hα0
    field_simp
  rw [← ENNReal.ofReal_mul hαnn, hEqReal]

/-- Inner equals the `Ioc` indicator for all `α ≠ b`. -/
lemma inner_eq_indicator_of_ne (b : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) (n : ℕ)
    (α : ℝ) (hne : α ≠ b) :
    (∫⁻ u : Fin n → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (α, u))) ∂volume)
      = (Set.Ioc b (1/2 : ℝ)).indicator (fun a => ENNReal.ofReal
        (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a * ((n+1).factorial : ℝ))) α := by
  by_cases hmem : α ∈ Set.Ioc b (1/2 : ℝ)
  · obtain ⟨hbα, ha2⟩ := Set.mem_Ioc.mp hmem
    have hab : b ≤ α := le_of_lt hbα
    rw [Set.indicator_of_mem hmem]
    exact inner_eq_H_of_mem b hb n α hab ha2
  · rw [Set.indicator_of_notMem hmem]
    by_cases hlt : α < b
    · have hle : ¬ b ≤ α := not_le.mpr hlt
      exact inner_zero_of_not_le b n α hle
    · have hle_bα : b ≤ α := le_of_not_gt hlt
      have hbα_lt : b < α := lt_of_le_of_ne hle_bα (Ne.symm hne)
      have ha : 1 / 2 < α := lt_of_not_ge (fun hle => hmem ⟨hbα_lt, hle⟩)
      exact inner_zero_of_gt_half b hb n α ha

/-- Distinguished piece lintegral equals RHS lintegral (α-outer Tonelli, inner = densityTerm). -/
lemma piece0_eq_rhs_lin (b : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) (n : ℕ) :
    (∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume)
      = ∫⁻ a : ℝ in Set.Ioc b (1/2), ENNReal.ofReal (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a * ((n+1).factorial : ℝ)) ∂volume := by
  classical
  have hG0 : Measurable (fun t : Fin (n+1) → ℝ =>
      ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t)) :=
    (outerF_meas b n |>.indicator ((outer_meas_sets b n).2.1)).ennreal_ofReal
  have e0s_meas : Measurable
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.measurable
  have hJ0 : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      ENNReal.ofReal ((piece0 b n).indicator (outerF b n)
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm p))) :=
    hG0.comp e0s_meas
  rw [transfer_lin_prod _ _ hG0, lintegral_prod _ hJ0.aemeasurable]
  -- RHS as un-restricted lintegral of indicator.
  have hIoc : MeasurableSet (Set.Ioc b (1/2 : ℝ)) := measurableSet_Ioc
  have hRHS : (∫⁻ a : ℝ in Set.Ioc b (1/2), ENNReal.ofReal
      (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a * ((n+1).factorial : ℝ)) ∂volume)
      = ∫⁻ α : ℝ, (Set.Ioc b (1/2 : ℝ)).indicator (fun a => ENNReal.ofReal
        (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a * ((n+1).factorial : ℝ))) α ∂volume := by
    rw [lintegral_indicator hIoc]
  rw [hRHS]
  -- Inner integral equals indicator a.e. (differ at most at `{b}`).
  apply lintegral_congr_ae
  have hnull : (volume : Measure ℝ) ({b} : Set ℝ) = 0 := by simp
  have hae : ∀ᵐ α ∂(volume : Measure ℝ), α ∉ ({b} : Set ℝ) :=
    compl_mem_ae_iff.mpr hnull
  filter_upwards [hae] with α hα
  have hne : α ≠ b := by simpa using hα
  exact inner_eq_indicator_of_ne b hb hb2 n α hne

/-- Per-`l` minimum-coordinate identity, indexed by `n` so `Fin` has no subtraction:
outer `n+2` corresponds to inner `n+1`. -/
lemma perL_identity (b : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) (n : ℕ) :
    densityTerm b 1 (n + 2) / ((n + 2).factorial : ℝ) =
      ∫ a : ℝ in b..(1 / 2 : ℝ), densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a := by
  classical
  have hb_le : b ≤ 1 / 2 := le_of_lt hb2
  have hfact1_pos : (0:ℝ) < ((n + 1).factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos _
  have hfact2_pos : (0:ℝ) < ((n + 2).factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos _
  have hfact1_ne : ((n + 1).factorial : ℝ) ≠ 0 := ne_of_gt hfact1_pos
  have hfact2_ne : ((n + 2).factorial : ℝ) ≠ 0 := ne_of_gt hfact2_pos
  -- Total lintegral = (n+2) • piece0.
  have hTotalEq : (∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal (outerF b n t) ∂volume)
      = (n + 2) • (∫⁻ t : Fin (n+1) → ℝ,
        ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume) := by
    have hSumEq : (∑ j : Fin (n+1), ∫⁻ t : Fin (n+1) → ℝ,
          ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) t) ∂volume)
        = (n + 1) • (∫⁻ t : Fin (n+1) → ℝ,
          ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume) := by
      have h1 : ∀ j : Fin (n+1), (∫⁻ t : Fin (n+1) → ℝ,
            ENNReal.ofReal ((pieceJ b n j).indicator (outerF b n) t) ∂volume)
          = (∫⁻ t : Fin (n+1) → ℝ,
            ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume) :=
        fun j => pieces_eq_indep_lin b hb n j
      rw [Finset.sum_congr rfl (fun j _ => h1 j)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [total_eq_sum_pieces_lin b hb n, hSumEq,
      pieceLast_eq_piece0_lin b hb hb2 n]
    -- `(n+1)•c + c = (n+2)•c`.
    have hEq : (n + 1) + 1 = n + 2 := rfl
    have hAdd : ((n + 1) + 1) • (∫⁻ t : Fin (n+1) → ℝ,
        ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume)
        = (n + 1) • (∫⁻ t : Fin (n+1) → ℝ,
          ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume)
          + 1 • (∫⁻ t : Fin (n+1) → ℝ,
            ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume) :=
      add_nsmul _ _ _
    rw [one_nsmul, hEq] at hAdd
    exact hAdd.symm
  -- Piece0 = RHS lintegral (before factorial simplification).
  have hPieceEq := piece0_eq_rhs_lin b hb hb2 n
  -- Simplify `D/((n+1)!)/a * (n+1)! = D/a` pointwise (as ENNReal).
  have hRHSimp : (∫⁻ a : ℝ in Set.Ioc b (1/2), ENNReal.ofReal
        (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a * ((n + 1).factorial : ℝ)) ∂volume)
        = ∫⁻ a : ℝ in Set.Ioc b (1/2),
          ENNReal.ofReal (densityTerm a (1 - a) (n + 1) / a) ∂volume := by
    apply lintegral_congr_ae
    apply ae_of_all
    intro a
    show ENNReal.ofReal (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a
        * ((n + 1).factorial : ℝ))
      = ENNReal.ofReal (densityTerm a (1 - a) (n + 1) / a)
    have hEqReal : densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a
          * ((n + 1).factorial : ℝ)
        = densityTerm a (1 - a) (n + 1) / a := by
      field_simp
    rw [hEqReal]
  -- Total `ofReal` correspondence.
  have hTotalOfReal : ENNReal.ofReal (densityTerm b 1 (n + 2))
      = (∫⁻ t : Fin (n+1) → ℝ, ENNReal.ofReal (outerF b n t) ∂volume) := by
    have hDT : densityTerm b 1 (n + 2) = ∫ t : Fin (n+1) → ℝ, outerF b n t ∂volume := rfl
    rw [hDT]
    have hInt : Integrable (outerF b n) volume :=
      integrable_outerF b hb hb2 n
    have hnn : 0 ≤ᵐ[volume] (outerF b n) := by
      apply Filter.Eventually.of_forall
      intro t
      exact outerF_nn b hb.le n t
    exact ofReal_integral_eq_lintegral_ofReal hInt hnn
  -- RHS `ofReal` correspondence: `ofReal(∫_{b..1/2} f) = ∫⁻_{Ioc} ofReal(f)`.
  have hRHSOfReal : ENNReal.ofReal
        (∫ a : ℝ in b..(1/2 : ℝ), densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a)
      = (∫⁻ a : ℝ in Set.Ioc b (1/2), ENNReal.ofReal
          (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) ∂volume) := by
    have hInt_eq : (∫ a : ℝ in b..(1/2 : ℝ),
          densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a)
        = ∫ a : ℝ in Set.Ioc b (1/2),
          densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a ∂volume :=
      intervalIntegral.integral_of_le hb_le
    rw [hInt_eq]
    -- `IntegrableOn` for `f` on `Ioc`.
    have hmeas_f : Measurable (fun a : ℝ =>
        densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) := by
      have hm1 : Measurable (fun a : ℝ => densityTerm a (1 - a) (n + 1)) :=
        (stronglyMeasurable_density_in_a (n + 1)).measurable
      exact (hm1.div_const _).div measurable_id
    have hfin_ne : (volume : Measure ℝ) (Set.Ioc b (1/2)) ≠ ∞ := by
      have hvol : (volume : Measure ℝ) (Set.Ioc b (1/2)) = ENNReal.ofReal (1/2 - b) :=
        Real.volume_Ioc
      rw [hvol]
      exact ENNReal.ofReal_ne_top
    obtain ⟨C, hC⟩ := bound_densityTerm_div b hb (n + 1)
    have hIntOn : IntegrableOn (fun a : ℝ =>
        densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a)
        (Set.Ioc b (1/2)) volume := by
      apply Measure.integrableOn_of_bounded hfin_ne hmeas_f.aestronglyMeasurable
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro a ha
      simp only [Set.mem_Ioc] at ha
      obtain ⟨hba, ha2⟩ := ha
      have hle := hC a hba.le ha2
      exact hle
    have hnnOn : 0 ≤ᵐ[volume.restrict (Set.Ioc b (1/2))]
        (fun a : ℝ => densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) := by
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro a ha
      simp only [Set.mem_Ioc] at ha
      obtain ⟨hbα, ha2⟩ := ha
      have ha0 : 0 < a := lt_trans hb hbα
      have hDnn : 0 ≤ densityTerm a (1 - a) (n + 1) :=
        densityTerm_nonneg ha0.le _
      have hfact_nn : 0 ≤ ((n + 1).factorial : ℝ) := Nat.cast_nonneg _
      have h1 : 0 ≤ densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) :=
        div_nonneg hDnn hfact_nn
      exact div_nonneg h1 ha0.le
    exact ofReal_integral_eq_lintegral_ofReal hIntOn hnnOn
  -- Combine: `ofReal(D_out) = ofReal((n+2)*((n+1)!*RHS))`, then `ofReal` injectivity + field.
  have hDout_nn : 0 ≤ densityTerm b 1 (n + 2) :=
    densityTerm_nonneg (le_of_lt hb) _
  have hRHS_nn : 0 ≤ (∫ a : ℝ in b..(1/2 : ℝ),
      densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) := by
    apply intervalIntegral.integral_nonneg hb_le
    intro u hu
    simp only [Set.mem_Icc] at hu
    obtain ⟨hbu, hu2⟩ := hu
    have hu0 : 0 < u := lt_of_lt_of_le hb hbu
    have hDnn : 0 ≤ densityTerm u (1 - u) (n + 1) :=
      densityTerm_nonneg hu0.le _
    have hfact_nn : 0 ≤ ((n + 1).factorial : ℝ) := Nat.cast_nonneg _
    have h1 : 0 ≤ densityTerm u (1 - u) (n + 1) / ((n + 1).factorial : ℝ) :=
      div_nonneg hDnn hfact_nn
    exact div_nonneg h1 hu0.le
  -- `piece0 = ofReal((n+1)!) * ofReal(RHS)` via const mul.
  have hPieceEq2 : (∫⁻ t : Fin (n+1) → ℝ,
        ENNReal.ofReal ((piece0 b n).indicator (outerF b n) t) ∂volume)
      = ENNReal.ofReal (((n + 1).factorial : ℝ))
        * ENNReal.ofReal (∫ a : ℝ in b..(1/2 : ℝ),
          densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) := by
    rw [hPieceEq, hRHSimp]
    -- Now `∫⁻ Ioc ofReal(D/a) = ofReal((n+1)!) * ∫⁻ Ioc ofReal(D/((n+1)!)/a)`.
    have hfact_nn : 0 ≤ ((n + 1).factorial : ℝ) := Nat.cast_nonneg _
    have hmeas_Ioc : Measurable (fun a : ℝ => ENNReal.ofReal
        (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a)) := by
      have hm1 : Measurable (fun a : ℝ => densityTerm a (1 - a) (n + 1)) :=
        (stronglyMeasurable_density_in_a (n + 1)).measurable
      exact ((hm1.div_const _).div measurable_id).ennreal_ofReal
    have hEq1 : (∫⁻ a : ℝ in Set.Ioc b (1/2),
          ENNReal.ofReal (densityTerm a (1 - a) (n + 1) / a) ∂volume)
        = ENNReal.ofReal (((n + 1).factorial : ℝ)) * ∫⁻ a : ℝ in Set.Ioc b (1/2),
          ENNReal.ofReal (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) ∂volume := by
      have hpoint : ∀ a : ℝ, ENNReal.ofReal (densityTerm a (1 - a) (n + 1) / a)
          = ENNReal.ofReal (((n + 1).factorial : ℝ))
            * ENNReal.ofReal (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) := by
        intro a
        have hEqReal : densityTerm a (1 - a) (n + 1) / a
            = ((n + 1).factorial : ℝ)
              * (densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) := by
          field_simp
        rw [hEqReal, ENNReal.ofReal_mul hfact_nn]
      rw [lintegral_congr_ae (ae_of_all _ fun a => hpoint a)]
      exact lintegral_const_mul _ hmeas_Ioc
    rw [hEq1, ← hRHSOfReal]
  -- `ofReal(D_out) = ofReal((n+2)*(fact1*RHS))`.
  have hOfRealEq : ENNReal.ofReal (densityTerm b 1 (n + 2))
      = ENNReal.ofReal (((n + 2 : ℕ) : ℝ)
        * (((n + 1).factorial : ℝ)
          * (∫ a : ℝ in b..(1/2 : ℝ),
            densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a))) := by
    have hTotal : ENNReal.ofReal (densityTerm b 1 (n + 2))
        = (n + 2) • (ENNReal.ofReal (((n + 1).factorial : ℝ))
          * ENNReal.ofReal (∫ a : ℝ in b..(1/2 : ℝ),
            densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a)) := by
      rw [hTotalOfReal, hTotalEq, hPieceEq2]
    -- Convert `(n+2)•(ofReal(fact)*ofReal(RHS))` to `ofReal((n+2)*(fact*RHS))`.
    have hfact1_nn : 0 ≤ ((n + 1).factorial : ℝ) := Nat.cast_nonneg _
    have hn2_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hRHS_nn' : 0 ≤ (∫ a : ℝ in b..(1/2 : ℝ),
        densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) := hRHS_nn
    have hprod1_nn : 0 ≤ ((n + 1).factorial : ℝ)
        * (∫ a : ℝ in b..(1/2 : ℝ),
          densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) :=
      mul_nonneg hfact1_nn hRHS_nn'
    have hnsmul_eq : (n + 2) • (ENNReal.ofReal (((n + 1).factorial : ℝ))
          * ENNReal.ofReal (∫ a : ℝ in b..(1/2 : ℝ),
            densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a))
        = ENNReal.ofReal (((n + 2 : ℕ) : ℝ))
          * (ENNReal.ofReal (((n + 1).factorial : ℝ))
            * ENNReal.ofReal (∫ a : ℝ in b..(1/2 : ℝ),
              densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a)) := by
      rw [nsmul_eq_mul]
      congr 1
      rw [← ENNReal.ofReal_natCast (n + 2)]
    rw [hnsmul_eq] at hTotal
    have hmul_eq : ENNReal.ofReal (((n + 2 : ℕ) : ℝ))
          * (ENNReal.ofReal (((n + 1).factorial : ℝ))
            * ENNReal.ofReal (∫ a : ℝ in b..(1/2 : ℝ),
              densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a))
        = ENNReal.ofReal (((n + 2 : ℕ) : ℝ)
          * (((n + 1).factorial : ℝ)
            * (∫ a : ℝ in b..(1/2 : ℝ),
              densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a))) := by
      rw [ENNReal.ofReal_mul hn2_nn, ENNReal.ofReal_mul hfact1_nn]
    rw [hmul_eq] at hTotal
    exact hTotal
  -- `ofReal` injectivity gives real equality.
  have hfact1_nn : 0 ≤ ((n + 1).factorial : ℝ) := Nat.cast_nonneg _
  have hn2_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hprod_nn : 0 ≤ ((n + 2 : ℕ) : ℝ)
      * (((n + 1).factorial : ℝ)
        * (∫ a : ℝ in b..(1/2 : ℝ),
          densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a)) :=
    mul_nonneg hn2_nn (mul_nonneg hfact1_nn hRHS_nn)
  have hRealEq : densityTerm b 1 (n + 2)
      = ((n + 2 : ℕ) : ℝ)
        * (((n + 1).factorial : ℝ)
          * (∫ a : ℝ in b..(1/2 : ℝ),
            densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a)) :=
    (ENNReal.ofReal_eq_ofReal_iff hDout_nn hprod_nn).mp hOfRealEq
  -- Factorial successor: `(n+2)! = (n+2)*(n+1)!`.
  have hFactSuccNat : (n + 2).factorial = (n + 2) * (n + 1).factorial :=
    Nat.factorial_succ (n + 1)
  have hFactSucc : ((n + 2).factorial : ℝ)
      = ((n + 2 : ℕ) : ℝ) * ((n + 1).factorial : ℝ) := by
    rw [hFactSuccNat]
    exact_mod_cast rfl
  -- Divide to get `perL`.
  have hn2_ne : ((n + 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n + 2 ≠ 0)
  have hEq : densityTerm b 1 (n + 2) / ((n + 2).factorial : ℝ)
      = (∫ a : ℝ in b..(1/2 : ℝ),
        densityTerm a (1 - a) (n + 1) / ((n + 1).factorial : ℝ) / a) := by
    rw [hRealEq, hFactSucc]
    field_simp
  exact hEq

lemma floor_mono_bound (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : b ≤ a) (ha2 : a ≤ 1 / 2) :
    ⌊(1 - a) / a⌋₊ ≤ ⌊1 / b⌋₊ := by
  apply Nat.floor_mono
  have ha0 : 0 < a := lt_of_lt_of_le hb ha
  have h1 : (1 - a) / a ≤ 1 / b := by
    have hdiv : (1 - a) / a = 1 / a - 1 := by
      field_simp
    rw [hdiv]
    have hle : 1 / a ≤ 1 / b := one_div_le_one_div_of_le hb ha
    linarith
  exact h1

lemma densityTerm_eq_zero_of_floor_lt {γ w : ℝ} (hγ : 0 < γ) (l : ℕ)
    (h : ⌊w / γ⌋₊ < l) : densityTerm γ w l = 0 := by
  apply densityTerm_eq_zero_of_lt (le_of_lt hγ)
  have h1 : w / γ < (⌊w / γ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : ⌊w / γ⌋₊ + 1 ≤ l := Nat.succ_le_of_lt h
  have h3 : (⌊w / γ⌋₊ : ℝ) + 1 ≤ (l : ℝ) := by
    exact_mod_cast h2
  have hlt : w / γ < (l : ℝ) := lt_of_lt_of_le h1 h3
  rwa [div_lt_iff₀ hγ] at hlt

theorem DensityIntegralTask_proof : DensityIntegralTask := by
  intro b hb hb2
  -- Let `N = ⌊1/b⌋₊ ≥ 2`.
  set N : ℕ := ⌊1 / b⌋₊ with hN
  have h1b : (2:ℝ) < 1 / b := by
    rw [lt_div_iff₀ hb]
    linarith
  have hNge : 2 ≤ N := by
    have : ((2 : ℕ) : ℝ) ≤ 1 / b := by
      exact_mod_cast le_of_lt h1b
    exact Nat.le_floor this
  -- Unfold `roughDensity b 1`.
  have hRD_b : roughDensity b 1 = 1 + ∑ l ∈ Finset.Icc 2 N, densityTerm b 1 l / (l.factorial : ℝ) := by
    unfold roughDensity
    simp only [inv_one, hN]
  -- For `a ∈ [b, 1/2]`, unfold `roughDensity a (1-a)` as a sum up to `N`.
  have hRD_a : ∀ a : ℝ, b ≤ a → a ≤ 1 / 2 →
      roughDensity a (1 - a) = ∑ l ∈ Finset.Icc 1 N, densityTerm a (1 - a) l / (l.factorial : ℝ) := by
    intro a hab ha2
    have ha0 : 0 < a := lt_of_lt_of_le hb hab
    have hM_le : ⌊(1 - a) / a⌋₊ ≤ N := floor_mono_bound b hb a hab ha2
    have hw1 : (1 - a)⁻¹ = densityTerm a (1 - a) 1 := by
      rw [densityTerm_one, if_pos (by linarith)]
    have hRD_unfold : roughDensity a (1 - a)
        = (1 - a)⁻¹ + ∑ l ∈ Finset.Icc 2 ⌊(1 - a) / a⌋₊, densityTerm a (1 - a) l / (l.factorial : ℝ) := rfl
    have h_extend : (∑ l ∈ Finset.Icc 2 ⌊(1 - a) / a⌋₊, densityTerm a (1 - a) l / (l.factorial : ℝ))
        = ∑ l ∈ Finset.Icc 2 N, densityTerm a (1 - a) l / (l.factorial : ℝ) := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right hM_le)
      intro l hlN hlnM
      simp only [Finset.mem_Icc] at hlN hlnM
      push_neg at hlnM
      have hlt : ⌊(1 - a) / a⌋₊ < l := by omega
      rw [densityTerm_eq_zero_of_floor_lt ha0 l hlt]
      simp
    have h1eq : densityTerm a (1 - a) 1 / ((Nat.factorial 1 : ℕ) : ℝ)
        = densityTerm a (1 - a) 1 := by simp
    have hsplit : (∑ l ∈ Finset.Icc 1 N, densityTerm a (1 - a) l / (l.factorial : ℝ))
        = densityTerm a (1 - a) 1 / ((Nat.factorial 1 : ℕ) : ℝ)
          + ∑ l ∈ Finset.Icc 2 N, densityTerm a (1 - a) l / (l.factorial : ℝ) := by
      have hN1 : 1 ≤ N := le_trans (by norm_num) hNge
      have hdisj : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 N) := by
        rw [Finset.disjoint_singleton_left]
        simp
      have hsplit2 : Finset.Icc 1 N = {1} ∪ Finset.Icc 2 N := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
        omega
      rw [hsplit2, Finset.sum_union hdisj]
      simp
    calc roughDensity a (1 - a)
        = (1 - a)⁻¹ + ∑ l ∈ Finset.Icc 2 ⌊(1 - a) / a⌋₊, densityTerm a (1 - a) l / (l.factorial : ℝ) := hRD_unfold
      _ = densityTerm a (1 - a) 1 + ∑ l ∈ Finset.Icc 2 ⌊(1 - a) / a⌋₊, densityTerm a (1 - a) l / (l.factorial : ℝ) := by rw [← hw1]
      _ = densityTerm a (1 - a) 1 + ∑ l ∈ Finset.Icc 2 N, densityTerm a (1 - a) l / (l.factorial : ℝ) := by rw [h_extend]
      _ = densityTerm a (1 - a) 1 / ((Nat.factorial 1 : ℕ) : ℝ) + ∑ l ∈ Finset.Icc 2 N, densityTerm a (1 - a) l / (l.factorial : ℝ) := by rw [h1eq]
      _ = ∑ l ∈ Finset.Icc 1 N, densityTerm a (1 - a) l / (l.factorial : ℝ) := by rw [← hsplit]
  -- Rewrite the integrand as a finite sum.
  have hb_le : b ≤ 1 / 2 := le_of_lt hb2
  have hEqOn : Set.EqOn (fun a : ℝ => roughDensity a (1 - a) / a)
      (fun a : ℝ => ∑ l ∈ Finset.Icc 1 N, (densityTerm a (1 - a) l / (l.factorial : ℝ) / a))
      (Set.uIcc b (1/2)) := by
    intro a ha
    have haIcc : a ∈ Set.Icc b (1/2:ℝ) := by
      have : Set.uIcc b (1/2:ℝ) = Set.Icc b (1/2:ℝ) := Set.uIcc_of_le hb_le
      rwa [this] at ha
    simp only [Set.mem_Icc] at haIcc
    obtain ⟨hba, ha2⟩ := haIcc
    show roughDensity a (1 - a) / a
      = ∑ l ∈ Finset.Icc 1 N, (densityTerm a (1 - a) l / (l.factorial : ℝ) / a)
    rw [hRD_a a hba ha2, Finset.sum_div]
  have h_int_congr : (∫ a : ℝ in b..(1/2:ℝ), roughDensity a (1 - a) / a)
      = (∫ a : ℝ in b..(1/2:ℝ), ∑ l ∈ Finset.Icc 1 N, (densityTerm a (1 - a) l / (l.factorial : ℝ) / a)) :=
    intervalIntegral.integral_congr hEqOn
  have h_int_sum : (∫ a : ℝ in b..(1/2:ℝ), ∑ l ∈ Finset.Icc 1 N, (densityTerm a (1 - a) l / (l.factorial : ℝ) / a))
      = ∑ l ∈ Finset.Icc 1 N, ∫ a : ℝ in b..(1/2:ℝ), densityTerm a (1 - a) l / (l.factorial : ℝ) / a := by
    apply intervalIntegral.integral_finsetSum
    intro l hl
    exact intervalIntegrable_densityTerm_div b hb l
  have h_int_eq : (∫ a : ℝ in b..(1/2:ℝ), roughDensity a (1 - a) / a)
      = ∑ l ∈ Finset.Icc 1 N, ∫ a : ℝ in b..(1/2:ℝ), densityTerm a (1 - a) l / (l.factorial : ℝ) / a := by
    rw [h_int_congr, h_int_sum]
  -- Each inner integral equals the next outer term by `perL_identity`.
  have h_perL_each : ∀ l ∈ Finset.Icc 1 N,
      (∫ a : ℝ in b..(1/2:ℝ), densityTerm a (1 - a) l / (l.factorial : ℝ) / a)
        = densityTerm b 1 (l + 1) / (((l + 1).factorial : ℕ) : ℝ) := by
    intro l hl
    simp only [Finset.mem_Icc] at hl
    obtain ⟨hl1, hlN⟩ := hl
    have hn : l - 1 + 1 = l := Nat.sub_add_cancel hl1
    have hn2 : l - 1 + 2 = l + 1 := by omega
    have hper := perL_identity b hb hb2 (l - 1)
    -- `hper : F_{(l-1)+2}/... = ∫ G_{(l-1)+1}/.../a`
    have h1 : densityTerm b 1 (l - 1 + 2) / ((((l - 1 + 2).factorial : ℕ)) : ℝ)
        = densityTerm b 1 (l + 1) / (((l + 1).factorial : ℕ) : ℝ) := by
      rw [hn2]
    have h2 : (∫ a : ℝ in b..(1/2:ℝ), densityTerm a (1 - a) (l - 1 + 1) / ((((l - 1 + 1).factorial : ℕ)) : ℝ) / a)
        = (∫ a : ℝ in b..(1/2:ℝ), densityTerm a (1 - a) l / (l.factorial : ℝ) / a) := by
      rw [hn]
    rw [h1, h2] at hper
    exact hper.symm
  have h_sum_perL : (∑ l ∈ Finset.Icc 1 N, ∫ a : ℝ in b..(1/2:ℝ), densityTerm a (1 - a) l / (l.factorial : ℝ) / a)
      = ∑ l ∈ Finset.Icc 1 N, (densityTerm b 1 (l + 1) / (((l + 1).factorial : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro l hl
    exact h_perL_each l hl
  -- Reindex `l ↦ l+1` to get `Icc 2 (N+1)`.
  have h_reindex : (∑ l ∈ Finset.Icc 1 N, (densityTerm b 1 (l + 1) / (((l + 1).factorial : ℕ) : ℝ)))
      = ∑ k ∈ Finset.Icc 2 (N + 1), (densityTerm b 1 k / ((k.factorial : ℕ) : ℝ)) := by
    have himg : Finset.image (fun l : ℕ => l + 1) (Finset.Icc 1 N) = Finset.Icc 2 (N + 1) := by
      ext k
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨l, ⟨hl1, hlN⟩, rfl⟩
        constructor <;> omega
      · intro hk
        obtain ⟨hk2, hkN⟩ := hk
        refine ⟨k - 1, ⟨by omega, by omega⟩, by omega⟩
    have hInj : Set.InjOn (fun l : ℕ => l + 1) ↑(Finset.Icc 1 N) := by
      intro x hx y hy hxy
      simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
      simp only at hxy
      omega
    have h_sum_img := Finset.sum_image hInj
      (f := fun k : ℕ => densityTerm b 1 k / ((k.factorial : ℕ) : ℝ))
    rw [himg] at h_sum_img
    exact h_sum_img.symm
  -- Drop the last zero term `N+1`.
  have h_last_zero : densityTerm b 1 (N + 1) / (((N + 1).factorial : ℕ) : ℝ) = 0 := by
    have hlt : ⌊1 / b⌋₊ < N + 1 := by omega
    rw [hN] at hlt
    -- Actually `N = ⌊1/b⌋₊`, so `N < N+1`, hence `floor < N+1`.
    have h0 : densityTerm b 1 (N + 1) = 0 :=
      densityTerm_eq_zero_of_floor_lt hb (N + 1) (by omega)
    rw [h0]
    simp
  have h_drop : (∑ k ∈ Finset.Icc 2 (N + 1), (densityTerm b 1 k / ((k.factorial : ℕ) : ℝ)))
      = ∑ k ∈ Finset.Icc 2 N, (densityTerm b 1 k / ((k.factorial : ℕ) : ℝ)) := by
    -- Need `2 ≤ N+1` for `sum_Icc_succ_top` with `a=2, b=N`.
    have h_eq := Finset.sum_Icc_succ_top (show 2 ≤ N + 1 by omega)
      (fun k => densityTerm b 1 k / ((k.factorial : ℕ) : ℝ))
    -- `h_eq : ∑ Icc 2 (N+1) = ∑ Icc 2 N + F_{N+1}`
    rw [h_eq, h_last_zero, add_zero]
  calc (∫ a : ℝ in b..(1/2:ℝ), roughDensity a (1 - a) / a)
      = ∑ l ∈ Finset.Icc 1 N, ∫ a : ℝ in b..(1/2:ℝ), densityTerm a (1 - a) l / (l.factorial : ℝ) / a := h_int_eq
    _ = ∑ l ∈ Finset.Icc 1 N, (densityTerm b 1 (l + 1) / (((l + 1).factorial : ℕ) : ℝ)) := h_sum_perL
    _ = ∑ k ∈ Finset.Icc 2 (N + 1), (densityTerm b 1 k / ((k.factorial : ℕ) : ℝ)) := h_reindex
    _ = ∑ k ∈ Finset.Icc 2 N, (densityTerm b 1 k / ((k.factorial : ℕ) : ℝ)) := h_drop
    _ = roughDensity b 1 - 1 := by
        rw [hRD_b]
        ring

end Erdos821.P8Int
