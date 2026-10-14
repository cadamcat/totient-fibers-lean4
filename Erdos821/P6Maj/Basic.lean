import Erdos821.Blueprint.Analytic
import Mathlib

noncomputable section
open Filter
open scoped ContDiff

namespace Erdos821.P6Maj
open Erdos821.Blueprint.Analytic

/-- The §5 Cauchy majorants. Only the lower e edge moves, by L^(-Cs),
so every derivative costs a fixed power of L per order. Cs and all these
costs are fixed before K₀. A scaled smoothTransition construction suffices. -/
def DyadicMajorantsTask : Prop :=
  ∀ Cs : ℝ, 0 < Cs → ∃ C : ℝ, 0 < C ∧ ∃ bounds : ℕ → ℝ,
    (∀ j, 0 ≤ bounds j) ∧ ∀ᶠ x : ℝ in atTop,
      ∃ etae etan : ℝ → ℝ,
        ContDiff ℝ ∞ etae ∧ ContDiff ℝ ∞ etan ∧
        Function.support etae ⊆ Set.Icc (L x ^ (-Cs) / 2) 2 ∧
        Function.support etan ⊆ Set.Icc (1 / 2) 4 ∧
        (∀ y, 0 ≤ etae y ∧ etae y ≤ 1 ∧ 0 ≤ etan y ∧ etan y ≤ 1) ∧
        (∀ y ∈ Set.Icc (L x ^ (-Cs)) 1, etae y = 1) ∧
        (∀ y ∈ Set.Icc 1 2, etan y = 1) ∧
        ∀ j y, ‖iteratedDeriv j etae y‖ ≤ bounds j * L x ^ (C * (j + 1)) ∧
          ‖iteratedDeriv j etan y‖ ≤ bounds j * L x ^ (C * (j + 1))

-- Helpers for the smoothTransition construction.

private lemma S_eventually_zero {y : ℝ} (hy : y < 0) :
    Real.smoothTransition =ᶠ[nhds y] fun _ => 0 := by
  have hmem : Set.Iio (0 : ℝ) ∈ nhds y := Iio_mem_nhds hy
  filter_upwards [hmem] with z hz
  exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)

private lemma S_eventually_one {y : ℝ} (hy : 1 < y) :
    Real.smoothTransition =ᶠ[nhds y] fun _ => 1 := by
  have hmem : Set.Ioi (1 : ℝ) ∈ nhds y := Ioi_mem_nhds hy
  filter_upwards [hmem] with z hz
  exact Real.smoothTransition.one_of_one_le (le_of_lt hz)

private lemma iteratedDeriv_S_zero_left {j : ℕ} (hj : j ≠ 0) {y : ℝ} (hy : y < 0) :
    iteratedDeriv j Real.smoothTransition y = 0 := by
  have h := (S_eventually_zero hy).iteratedDeriv_eq j
  simpa [hj] using h

private lemma iteratedDeriv_S_zero_right {j : ℕ} (hj : j ≠ 0) {y : ℝ} (hy : 1 < y) :
    iteratedDeriv j Real.smoothTransition y = 0 := by
  have h := (S_eventually_one hy).iteratedDeriv_eq j
  rw [iteratedDeriv_const] at h
  simp [hj] at h
  exact h

private lemma S_norm_le_one (y : ℝ) : ‖Real.smoothTransition y‖ ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg y
  have h1 := Real.smoothTransition.le_one y
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

private lemma exists_Sbound (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖iteratedDeriv j Real.smoothTransition y‖ ≤ B := by
  by_cases hj : j = 0
  · subst hj
    refine ⟨1, zero_le_one, fun y => ?_⟩
    simpa using S_norm_le_one y
  · have hcont : Continuous (iteratedDeriv j Real.smoothTransition) := by
      have hS : ContDiff ℝ (∞ : ℕ∞ω) Real.smoothTransition :=
        Real.smoothTransition.contDiff
      exact hS.continuous_iteratedDeriv j (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn
        (f := iteratedDeriv j Real.smoothTransition) hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy0 : y < 0
    · rw [iteratedDeriv_S_zero_left hj hy0, norm_zero]
      exact le_max_right _ _
    · by_cases hy1 : 1 < y
      · rw [iteratedDeriv_S_zero_right hj hy1, norm_zero]
        exact le_max_right _ _
      · have hmem : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_gt hy0, le_of_not_gt hy1⟩
        calc ‖iteratedDeriv j _ y‖ ≤ C := hC y hmem
          _ ≤ max C 0 := le_max_left _ _

-- Uniform bounds for the transition function itself.
private noncomputable def Sbound : ℕ → ℝ :=
  fun j => Classical.choose (exists_Sbound j)

private lemma hSbound_nonneg (j : ℕ) : 0 ≤ Sbound j :=
  (Classical.choose_spec (exists_Sbound j)).1

private lemma hSbound_le (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j Real.smoothTransition y‖ ≤ Sbound j :=
  (Classical.choose_spec (exists_Sbound j)).2 y

-- Affine reparametrizations.
private lemma iteratedDeriv_affine (a b : ℝ) (j : ℕ) (y : ℝ) :
    iteratedDeriv j (fun y : ℝ => Real.smoothTransition (a * y + b)) y =
      a ^ j * iteratedDeriv j Real.smoothTransition (a * y + b) := by
  have hg : ContDiff ℝ ((j : ℕ) : ℕ∞ω)
      (fun z : ℝ => Real.smoothTransition (z + b)) := by
    have hS : ContDiff ℝ ((j : ℕ) : ℕ∞ω) Real.smoothTransition :=
      (Real.smoothTransition.contDiff (n := ⊤)).of_le (by exact_mod_cast le_top)
    have haff : ContDiff ℝ ((j : ℕ) : ℕ∞ω) (fun z : ℝ => z + b) := by fun_prop
    exact hS.comp haff
  have hscale := iteratedDeriv_comp_const_mul (𝕜 := ℝ) (n := j)
    (f := fun z : ℝ => Real.smoothTransition (z + b)) hg a
  have htrans := iteratedDeriv_comp_add_const (𝕜 := ℝ) (n := j)
    (f := Real.smoothTransition) (s := b)
  have heq : (fun y : ℝ => Real.smoothTransition (a * y + b))
      = (fun y : ℝ => (fun z : ℝ => Real.smoothTransition (z + b)) (a * y)) := rfl
  rw [heq, congrFun hscale y]
  congr 1
  have h2 := congrFun htrans (a * y)
  simpa using h2

private lemma norm_iteratedDeriv_affine_le (a b : ℝ) (i : ℕ) (y : ℝ) :
    ‖iteratedDeriv i (fun y : ℝ => Real.smoothTransition (a * y + b)) y‖ ≤
      |a| ^ i * Sbound i := by
  rw [iteratedDeriv_affine a b i y]
  calc ‖a ^ i * iteratedDeriv i Real.smoothTransition (a * y + b)‖
      = ‖a ^ i‖ * ‖iteratedDeriv i Real.smoothTransition (a * y + b)‖ := norm_mul _ _
    _ = |a| ^ i * ‖iteratedDeriv i Real.smoothTransition (a * y + b)‖ := by
        rw [Real.norm_eq_abs, abs_pow]
    _ ≤ |a| ^ i * Sbound i := by
        exact mul_le_mul_of_nonneg_left (hSbound_le i _)
          (pow_nonneg (abs_nonneg _) _)

private lemma contDiff_affine_S (a b : ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (fun y : ℝ => Real.smoothTransition (a * y + b)) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

private lemma contDiffAt_affine_S (a b : ℝ) (j : ℕ) (y : ℝ) :
    ContDiffAt ℝ ((j : ℕ) : ℕ∞ω)
      (fun y : ℝ => Real.smoothTransition (a * y + b)) y :=
  ((contDiff_affine_S a b).contDiffAt).of_le (by exact_mod_cast le_top)

-- Product bound in terms of the uniform transition bounds.
private lemma norm_iteratedDeriv_mul_affine (a1 b1 a2 b2 : ℝ) (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j
        (fun y : ℝ => Real.smoothTransition (a1 * y + b1) *
          Real.smoothTransition (a2 * y + b2)) y‖ ≤
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (|a1| ^ i * Sbound i) * (|a2| ^ (j - i) * Sbound (j - i)) := by
  have h1 := contDiffAt_affine_S a1 b1 j y
  have h2 := contDiffAt_affine_S a2 b2 j y
  have hmul := iteratedDeriv_mul (𝕜 := ℝ) (n := j)
    (f := fun y : ℝ => Real.smoothTransition (a1 * y + b1))
    (g := fun y : ℝ => Real.smoothTransition (a2 * y + b2)) h1 h2
  have heq : (fun y : ℝ => Real.smoothTransition (a1 * y + b1) *
      Real.smoothTransition (a2 * y + b2))
      = ((fun y : ℝ => Real.smoothTransition (a1 * y + b1)) *
        (fun y : ℝ => Real.smoothTransition (a2 * y + b2))) := by
    rfl
  rw [heq, hmul]
  calc ‖∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * iteratedDeriv i _ y * iteratedDeriv (j - i) _ y‖
      ≤ ∑ i ∈ Finset.range (j + 1),
        ‖(j.choose i : ℝ) * iteratedDeriv i _ y * iteratedDeriv (j - i) _ y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (|a1| ^ i * Sbound i) * (|a2| ^ (j - i) * Sbound (j - i)) := by
        apply Finset.sum_le_sum
        intro i _
        have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
        have hri := norm_iteratedDeriv_affine_le a1 b1 i y
        have hfa := norm_iteratedDeriv_affine_le a2 b2 (j - i) y
        calc ‖(j.choose i : ℝ) * iteratedDeriv i _ y * iteratedDeriv (j - i) _ y‖
            = ‖(j.choose i : ℝ)‖ * (‖iteratedDeriv i _ y‖ * ‖iteratedDeriv (j - i) _ y‖) := by
              rw [norm_mul, norm_mul]
              ring
          _ = (j.choose i : ℝ) * (‖iteratedDeriv i _ y‖ * ‖iteratedDeriv (j - i) _ y‖) := by
              rw [Real.norm_eq_abs, abs_of_nonneg hc]
          _ ≤ (j.choose i : ℝ) * ((|a1| ^ i * Sbound i) * (|a2| ^ (j - i) * Sbound (j - i))) := by
              apply mul_le_mul_of_nonneg_left _ hc
              exact mul_le_mul hri hfa (norm_nonneg _)
                (mul_nonneg (pow_nonneg (abs_nonneg _) _) (hSbound_nonneg _))
          _ = _ := by ring

-- The concrete bump functions.
private noncomputable def riseE (δ : ℝ) : ℝ → ℝ :=
  fun y => Real.smoothTransition ((2 / δ) * y + (-1))

private noncomputable def fallE : ℝ → ℝ :=
  fun y => Real.smoothTransition ((-1) * y + 2)

private noncomputable def riseN : ℝ → ℝ :=
  fun y => Real.smoothTransition (2 * y + (-1))

private noncomputable def fallN : ℝ → ℝ :=
  fun y => Real.smoothTransition (((-1) / 2) * y + 2)

private noncomputable def etaeOf (δ : ℝ) : ℝ → ℝ :=
  fun y => riseE δ y * fallE y

private noncomputable def etanOf : ℝ → ℝ :=
  fun y => riseN y * fallN y

private lemma contDiff_riseE (δ : ℝ) : ContDiff ℝ (∞ : ℕ∞ω) (riseE δ) :=
  contDiff_affine_S _ _

private lemma contDiff_fallE : ContDiff ℝ (∞ : ℕ∞ω) fallE :=
  contDiff_affine_S _ _

private lemma contDiff_riseN : ContDiff ℝ (∞ : ℕ∞ω) riseN :=
  contDiff_affine_S _ _

private lemma contDiff_fallN : ContDiff ℝ (∞ : ℕ∞ω) fallN :=
  contDiff_affine_S _ _

private lemma contDiff_etaeOf (δ : ℝ) : ContDiff ℝ (∞ : ℕ∞ω) (etaeOf δ) :=
  (contDiff_riseE δ).mul contDiff_fallE

private lemma contDiff_etanOf : ContDiff ℝ (∞ : ℕ∞ω) etanOf :=
  contDiff_riseN.mul contDiff_fallN

-- Pointwise range for each factor.
private lemma riseE_nonneg (δ y : ℝ) : 0 ≤ riseE δ y :=
  Real.smoothTransition.nonneg _
private lemma riseE_le_one (δ y : ℝ) : riseE δ y ≤ 1 :=
  Real.smoothTransition.le_one _
private lemma fallE_nonneg (y : ℝ) : 0 ≤ fallE y :=
  Real.smoothTransition.nonneg _
private lemma fallE_le_one (y : ℝ) : fallE y ≤ 1 :=
  Real.smoothTransition.le_one _
private lemma riseN_nonneg (y : ℝ) : 0 ≤ riseN y :=
  Real.smoothTransition.nonneg _
private lemma riseN_le_one (y : ℝ) : riseN y ≤ 1 :=
  Real.smoothTransition.le_one _
private lemma fallN_nonneg (y : ℝ) : 0 ≤ fallN y :=
  Real.smoothTransition.nonneg _
private lemma fallN_le_one (y : ℝ) : fallN y ≤ 1 :=
  Real.smoothTransition.le_one _

private lemma riseE_eq_zero (δ : ℝ) (hδ : 0 < δ) {y : ℝ} (hy : y < δ / 2) :
    riseE δ y = 0 := by
  unfold riseE
  apply Real.smoothTransition.zero_of_nonpos
  have hae : (0 : ℝ) < 2 / δ := div_pos zero_lt_two hδ
  have h1 : (2 / δ) * y < (2 / δ) * (δ / 2) :=
    mul_lt_mul_of_pos_left hy hae
  have h2 : (2 / δ) * (δ / 2) = 1 := by field_simp
  linarith

private lemma riseE_eq_one (δ : ℝ) (hδ : 0 < δ) {y : ℝ} (hy : δ ≤ y) :
    riseE δ y = 1 := by
  unfold riseE
  apply Real.smoothTransition.one_of_one_le
  have hae : (0 : ℝ) ≤ 2 / δ := le_of_lt (div_pos zero_lt_two hδ)
  have h1 : (2 / δ) * δ ≤ (2 / δ) * y :=
    mul_le_mul_of_nonneg_left hy hae
  have h2 : (2 / δ) * δ = 2 := by field_simp
  linarith

private lemma fallE_eq_zero {y : ℝ} (hy : 2 < y) : fallE y = 0 := by
  unfold fallE
  apply Real.smoothTransition.zero_of_nonpos
  linarith

private lemma fallE_eq_one {y : ℝ} (hy : y ≤ 1) : fallE y = 1 := by
  unfold fallE
  apply Real.smoothTransition.one_of_one_le
  linarith

private lemma riseN_eq_zero {y : ℝ} (hy : y < 1 / 2) : riseN y = 0 := by
  unfold riseN
  apply Real.smoothTransition.zero_of_nonpos
  linarith

private lemma riseN_eq_one {y : ℝ} (hy : 1 ≤ y) : riseN y = 1 := by
  unfold riseN
  apply Real.smoothTransition.one_of_one_le
  linarith

private lemma fallN_eq_zero {y : ℝ} (hy : 4 < y) : fallN y = 0 := by
  unfold fallN
  apply Real.smoothTransition.zero_of_nonpos
  linarith

private lemma fallN_eq_one {y : ℝ} (hy : y ≤ 2) : fallN y = 1 := by
  unfold fallN
  apply Real.smoothTransition.one_of_one_le
  linarith

private lemma etaeOf_eq_zero_left (δ : ℝ) (hδ : 0 < δ) {y : ℝ} (hy : y < δ / 2) :
    etaeOf δ y = 0 := by
  unfold etaeOf
  rw [riseE_eq_zero δ hδ hy, zero_mul]

private lemma etaeOf_eq_zero_right (δ : ℝ) {y : ℝ} (hy : 2 < y) :
    etaeOf δ y = 0 := by
  unfold etaeOf
  rw [fallE_eq_zero hy, mul_zero]

private lemma etanOf_eq_zero_left {y : ℝ} (hy : y < 1 / 2) : etanOf y = 0 := by
  unfold etanOf
  rw [riseN_eq_zero hy, zero_mul]

private lemma etanOf_eq_zero_right {y : ℝ} (hy : 4 < y) : etanOf y = 0 := by
  unfold etanOf
  rw [fallN_eq_zero hy, mul_zero]

private lemma etaeOf_eq_one (δ : ℝ) (hδ : 0 < δ) {y : ℝ}
    (hy1 : δ ≤ y) (hy2 : y ≤ 1) : etaeOf δ y = 1 := by
  unfold etaeOf
  rw [riseE_eq_one δ hδ hy1, fallE_eq_one hy2, one_mul]

private lemma etanOf_eq_one {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 2) :
    etanOf y = 1 := by
  unfold etanOf
  rw [riseN_eq_one hy1, fallN_eq_one hy2, one_mul]

private lemma etaeOf_nonneg (δ y : ℝ) : 0 ≤ etaeOf δ y :=
  mul_nonneg (riseE_nonneg _ _) (fallE_nonneg _)

private lemma etaeOf_le_one (δ y : ℝ) : etaeOf δ y ≤ 1 := by
  have h1 := riseE_le_one δ y
  have h2 := fallE_le_one y
  have h0 := fallE_nonneg y
  calc riseE δ y * fallE y ≤ 1 * fallE y :=
        mul_le_mul_of_nonneg_right h1 h0
    _ = fallE y := one_mul _
    _ ≤ 1 := h2

private lemma etanOf_nonneg (y : ℝ) : 0 ≤ etanOf y :=
  mul_nonneg (riseN_nonneg _) (fallN_nonneg _)

private lemma etanOf_le_one (y : ℝ) : etanOf y ≤ 1 := by
  have h1 := riseN_le_one y
  have h2 := fallN_le_one y
  have h0 := fallN_nonneg y
  calc riseN y * fallN y ≤ 1 * fallN y :=
        mul_le_mul_of_nonneg_right h1 h0
    _ = fallN y := one_mul _
    _ ≤ 1 := h2

private lemma support_etaeOf (δ : ℝ) (hδ : 0 < δ) :
    Function.support (etaeOf δ) ⊆ Set.Icc (δ / 2) 2 := by
  intro y hy
  simp only [Function.mem_support, ne_eq] at hy
  by_cases h1 : y < δ / 2
  · exfalso; exact hy (etaeOf_eq_zero_left δ hδ h1)
  · by_cases h2 : 2 < y
    · exfalso; exact hy (etaeOf_eq_zero_right δ h2)
    · exact ⟨le_of_not_gt h1, le_of_not_gt h2⟩

private lemma support_etanOf :
    Function.support etanOf ⊆ Set.Icc (1 / 2) 4 := by
  intro y hy
  simp only [Function.mem_support, ne_eq] at hy
  by_cases h1 : y < 1 / 2
  · exfalso; exact hy (etanOf_eq_zero_left h1)
  · by_cases h2 : 4 < y
    · exfalso; exact hy (etanOf_eq_zero_right h2)
    · exact ⟨le_of_not_gt h1, le_of_not_gt h2⟩

-- Absolute values of the fixed scalings.
private lemma abs_two_div (δ : ℝ) (hδ : 0 < δ) : |2 / δ| = 2 / δ :=
  abs_of_pos (div_pos zero_lt_two hδ)

private lemma abs_neg_one : |(-1 : ℝ)| = 1 := by simp

private lemma abs_neg_half : |(((-1) / 2) : ℝ)| = 1 / 2 := by norm_num

private lemma abs_two : |(2 : ℝ)| = 2 := abs_of_pos zero_lt_two

-- Coefficient bounds built from the uniform transition bounds.
private noncomputable def Be (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * 2 ^ i * Sbound i * Sbound (j - i)

private noncomputable def Bn (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * 2 ^ i * ((1 / 2 : ℝ) ^ (j - i)) * Sbound i * Sbound (j - i)

private noncomputable def majorBounds (j : ℕ) : ℝ := max (Be j) (Bn j)

private lemma term_nonneg_e (j i : ℕ) :
    0 ≤ (j.choose i : ℝ) * 2 ^ i * Sbound i * Sbound (j - i) := by
  have hC : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ i := pow_nonneg (by norm_num) _
  have hSi : (0 : ℝ) ≤ Sbound i := hSbound_nonneg _
  have hSj : (0 : ℝ) ≤ Sbound (j - i) := hSbound_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg hC h2) hSi) hSj

private lemma term_nonneg_n (j i : ℕ) :
    0 ≤ (j.choose i : ℝ) * 2 ^ i * ((1 / 2 : ℝ) ^ (j - i)) * Sbound i * Sbound (j - i) := by
  have hC : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ i := pow_nonneg (by norm_num) _
  have h12 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j - i) := pow_nonneg (by norm_num) _
  have hSi : (0 : ℝ) ≤ Sbound i := hSbound_nonneg _
  have hSj : (0 : ℝ) ≤ Sbound (j - i) := hSbound_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC h2) h12) hSi) hSj

private lemma Be_nonneg (j : ℕ) : 0 ≤ Be j :=
  Finset.sum_nonneg fun i _ => term_nonneg_e j i

private lemma Bn_nonneg (j : ℕ) : 0 ≤ Bn j :=
  Finset.sum_nonneg fun i _ => term_nonneg_n j i

private lemma majorBounds_nonneg (j : ℕ) : 0 ≤ majorBounds j :=
  le_trans (Be_nonneg j) (le_max_left _ _)

private lemma norm_etanOf_le_Bn (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j etanOf y‖ ≤ Bn j := by
  have h := norm_iteratedDeriv_mul_affine (2 : ℝ) (-1) (((-1) / 2) : ℝ) (2 : ℝ) j y
  rw [abs_two, abs_neg_half] at h
  have heq : etanOf =
      (fun y : ℝ => Real.smoothTransition (2 * y + (-1)) *
        Real.smoothTransition (((-1) / 2) * y + 2)) := by
    rfl
  rw [heq]
  have hsum : (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (2 ^ i * Sbound i) * ((1 / 2 : ℝ) ^ (j - i) * Sbound (j - i)))
      = Bn j := by
    unfold Bn
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← hsum]
  exact h

private lemma norm_etaeOf_le_abs (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j (etaeOf δ) y‖ ≤
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ((2 / δ) ^ i * Sbound i) * Sbound (j - i) := by
  have h := norm_iteratedDeriv_mul_affine (2 / δ) (-1) (-1 : ℝ) (2 : ℝ) j y
  rw [abs_two_div δ hδ, abs_neg_one] at h
  have heq : etaeOf δ =
      (fun y : ℝ => Real.smoothTransition ((2 / δ) * y + (-1)) *
        Real.smoothTransition ((-1) * y + 2)) := by
    rfl
  rw [heq]
  have hsum : (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ((2 / δ) ^ i * Sbound i) * ((1 : ℝ) ^ (j - i) * Sbound (j - i)))
      = ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ((2 / δ) ^ i * Sbound i) * Sbound (j - i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [one_pow]
  rw [← hsum]
  exact h

private lemma pow_two_div_delta (x Cs : ℝ) (hLpos : 0 < L x) (i : ℕ) :
    ((2 / (L x ^ (-Cs))) ^ i : ℝ) = 2 ^ i * L x ^ (Cs * (i : ℝ)) := by
  have hLnonneg : 0 ≤ L x := le_of_lt hLpos
  have hδ : L x ^ (-Cs) = (L x ^ Cs)⁻¹ := Real.rpow_neg hLnonneg Cs
  have hδinv : (L x ^ (-Cs))⁻¹ = L x ^ Cs := by
    rw [hδ, inv_inv]
  have h2δ : (2 : ℝ) / (L x ^ (-Cs)) = 2 * L x ^ Cs := by
    rw [div_eq_mul_inv, hδinv]
  rw [h2δ, mul_pow]
  congr 1
  rw [← Real.rpow_natCast _ i, ← Real.rpow_mul hLnonneg]

private lemma exp_le_aux (Cs : ℝ) (hCs : 0 < Cs) (j i : ℕ) (hi : i ≤ j) :
    Cs * (i : ℝ) ≤ (Cs + 1) * ((j : ℝ) + 1) := by
  have hij : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hi
  calc Cs * (i : ℝ) ≤ Cs * (j : ℝ) :=
        mul_le_mul_of_nonneg_left hij (le_of_lt hCs)
    _ ≤ (Cs + 1) * ((j : ℝ) + 1) := by
        have heq : (Cs + 1) * ((j : ℝ) + 1) = Cs * (j : ℝ) + (Cs + (j : ℝ) + 1) := by
          ring
        rw [heq]
        apply le_add_of_nonneg_right
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        linarith

private lemma eventually_one_le_L : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := by
  have h : ∀ᶠ x : ℝ in Filter.atTop, Real.exp 1 ≤ x :=
    Filter.eventually_ge_atTop _
  filter_upwards [h] with x hx
  have hlog : Real.log (Real.exp 1) ≤ Real.log x :=
    Real.log_le_log (Real.exp_pos _) hx
  rw [Real.log_exp] at hlog
  show 1 ≤ L x
  rw [show L x = Real.log x from rfl]
  linarith

theorem DyadicMajorantsTask_proof : DyadicMajorantsTask := by
  intro Cs hCs
  refine ⟨Cs + 1, by linarith, majorBounds, majorBounds_nonneg, ?_⟩
  filter_upwards [eventually_one_le_L] with x hx
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hx
  have hδpos0 : 0 < L x ^ (-Cs) := Real.rpow_pos_of_pos hLpos _
  set δ : ℝ := L x ^ (-Cs) with hδdef
  have hδpos : 0 < δ := hδpos0
  refine ⟨etaeOf δ, etanOf, contDiff_etaeOf δ, contDiff_etanOf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- support etae
    have h := support_etaeOf δ hδpos
    simpa [hδdef] using h
  · exact support_etanOf
  · intro y
    exact ⟨etaeOf_nonneg δ y, etaeOf_le_one δ y, etanOf_nonneg y, etanOf_le_one y⟩
  · intro y hy
    simp only [Set.mem_Icc] at hy
    have hy1 : δ ≤ y := by rw [hδdef]; exact hy.1
    exact etaeOf_eq_one δ hδpos hy1 hy.2
  · intro y hy
    simp only [Set.mem_Icc] at hy
    exact etanOf_eq_one hy.1 hy.2
  · intro j y
    constructor
    · -- etae derivative bound
      have hCpos : (0 : ℝ) < Cs + 1 := by linarith
      have hj1pos : (0 : ℝ) < ((j : ℝ) + 1) := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        linarith
      have hExpNonneg : (0 : ℝ) ≤ (Cs + 1) * ((j : ℝ) + 1) :=
        le_of_lt (mul_pos hCpos hj1pos)
      have hLpow1 : (1 : ℝ) ≤ L x ^ ((Cs + 1) * ((j : ℝ) + 1)) :=
        Real.one_le_rpow hx hExpNonneg
      have hLpow_nonneg : (0 : ℝ) ≤ L x ^ ((Cs + 1) * ((j : ℝ) + 1)) :=
        Real.rpow_nonneg (le_of_lt hLpos) _
      have h_abs := norm_etaeOf_le_abs δ hδpos j y
      -- rewrite (2/δ)^i
      have hpow_eq : ∀ i ∈ Finset.range (j + 1),
          ((2 / δ) ^ i : ℝ) = 2 ^ i * L x ^ (Cs * (i : ℝ)) := by
        intro i _
        rw [hδdef]
        exact pow_two_div_delta x Cs hLpos i
      -- each term bound
      have hterm : ∀ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ((2 / δ) ^ i * Sbound i) * Sbound (j - i)
            ≤ ((j.choose i : ℝ) * 2 ^ i * Sbound i * Sbound (j - i))
              * L x ^ ((Cs + 1) * ((j : ℝ) + 1)) := by
        intro i hi
        have hi_le : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hexp := exp_le_aux Cs hCs j i hi_le
        have hrpow := Real.rpow_le_rpow_of_exponent_le hx hexp
        have hcoeff : (0 : ℝ) ≤ (j.choose i : ℝ) * 2 ^ i * Sbound i * Sbound (j - i) :=
          term_nonneg_e j i
        have hpow_rw : ((2 / δ) ^ i : ℝ) = 2 ^ i * L x ^ (Cs * (i : ℝ)) :=
          hpow_eq i hi
        calc (j.choose i : ℝ) * ((2 / δ) ^ i * Sbound i) * Sbound (j - i)
            = ((j.choose i : ℝ) * 2 ^ i * Sbound i * Sbound (j - i))
              * L x ^ (Cs * (i : ℝ)) := by
              rw [hpow_rw]; ring
          _ ≤ ((j.choose i : ℝ) * 2 ^ i * Sbound i * Sbound (j - i))
              * L x ^ ((Cs + 1) * ((j : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left hrpow hcoeff
      have hsum_le : (∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * ((2 / δ) ^ i * Sbound i) * Sbound (j - i))
          ≤ Be j * L x ^ ((Cs + 1) * ((j : ℝ) + 1)) := by
        calc (∑ i ∈ Finset.range (j + 1),
              (j.choose i : ℝ) * ((2 / δ) ^ i * Sbound i) * Sbound (j - i))
            ≤ ∑ i ∈ Finset.range (j + 1),
              (((j.choose i : ℝ) * 2 ^ i * Sbound i * Sbound (j - i))
                * L x ^ ((Cs + 1) * ((j : ℝ) + 1))) :=
              Finset.sum_le_sum hterm
          _ = Be j * L x ^ ((Cs + 1) * ((j : ℝ) + 1)) := by
              unfold Be
              rw [Finset.sum_mul]
      have hBe_le : Be j ≤ majorBounds j := le_max_left _ _
      calc ‖iteratedDeriv j (etaeOf δ) y‖
          ≤ ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * ((2 / δ) ^ i * Sbound i) * Sbound (j - i) := h_abs
        _ ≤ Be j * L x ^ ((Cs + 1) * ((j : ℝ) + 1)) := hsum_le
        _ ≤ majorBounds j * L x ^ ((Cs + 1) * ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hBe_le hLpow_nonneg
    · -- etan derivative bound
      have hCpos : (0 : ℝ) < Cs + 1 := by linarith
      have hj1pos : (0 : ℝ) < ((j : ℝ) + 1) := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        linarith
      have hExpNonneg : (0 : ℝ) ≤ (Cs + 1) * ((j : ℝ) + 1) :=
        le_of_lt (mul_pos hCpos hj1pos)
      have hLpow1 : (1 : ℝ) ≤ L x ^ ((Cs + 1) * ((j : ℝ) + 1)) :=
        Real.one_le_rpow hx hExpNonneg
      have hBn := norm_etanOf_le_Bn j y
      have hBn_le : Bn j ≤ majorBounds j := le_max_right _ _
      have hMb : (0 : ℝ) ≤ majorBounds j := majorBounds_nonneg j
      calc ‖iteratedDeriv j etanOf y‖
          ≤ Bn j := hBn
        _ ≤ majorBounds j := hBn_le
        _ = majorBounds j * 1 := (mul_one _).symm
        _ ≤ majorBounds j * L x ^ ((Cs + 1) * ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hLpow1 hMb


example : DyadicMajorantsTask := DyadicMajorantsTask_proof

end Erdos821.P6Maj
