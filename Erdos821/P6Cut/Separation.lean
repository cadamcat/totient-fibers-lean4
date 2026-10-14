import Erdos821.Blueprint.Classical

noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory

namespace Erdos821.P6Cut
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The exact smooth weights in logarithmic variables after determinant
reconstruction. The compact localization is fixed before all precisions. -/
def pulledCutoff (U V Z E : ℝ) (k : ℤ) (etae etan : ℝ → ℝ)
    (localizer : (Fin 3 → ℝ) → ℝ) (t : Fin 3 → ℝ) : ℂ :=
  let m := U * Real.exp (t 0)
  let m' := U * Real.exp (t 1)
  let z := Z * Real.exp (t 2)
  (localizer t * etae ((m' - m) / (2 * k * E)) *
    etan ((m' - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ)

/-- Quantitative three-variable Fourier separation. All exponents and
constants are fixed before the tail saving A and before discrepancy B. -/
def PulledCutoffSeparationTask : Prop :=
  ClassicalInputs →
  ∀ (C K0 CZ R : ℝ) (bounds localBounds : ℕ → ℝ)
    (localizer : (Fin 3 → ℝ) → ℝ),
    0 < C → 0 < K0 → 0 < CZ → 0 < R →
    (∀ j, 0 ≤ bounds j ∧ 0 ≤ localBounds j) →
    ContDiff ℝ ∞ localizer →
    Function.support localizer ⊆ Metric.closedBall 0 R →
    (∀ j y, ‖iteratedFDeriv ℝ j localizer y‖ ≤ localBounds j) →
    ∃ Cf K : ℝ, 0 < Cf ∧ 0 < K ∧
      ∀ A : ℝ, 0 < A → ∃ KA : ℝ, 0 < KA ∧ ∀ᶠ x : ℝ in atTop,
        ∀ (U V Z : ℝ) (k : ℤ) (etae etan : ℝ → ℝ),
          1 ≤ U → 1 ≤ V → x / 8 ≤ U * V → U * V ≤ 8 * x →
          0 < Z → Z ≤ x * L x ^ CZ → k ≠ 0 →
          ContDiff ℝ ∞ etae → ContDiff ℝ ∞ etan →
          (∀ j y, ‖iteratedDeriv j etae y‖ ≤ bounds j * L x ^ (C * (j + 1)) ∧
            ‖iteratedDeriv j etan y‖ ≤ bounds j * L x ^ (C * (j + 1))) →
          ∃ a : (Fin 3 → ℝ) → ℂ,
            Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ K ∧
            (∀ t, pulledCutoff U V Z (U * L x ^ (-K0)) k etae etan localizer t =
              ∫ ξ, a ξ * e (∑ i, ξ i * t i)) ∧
            (∫ ξ in {ξ : Fin 3 → ℝ | L x ^ Cf < ‖ξ‖}, ‖a ξ‖) ≤
              KA * L x ^ (-A)

-- Helper: 1D exp has all iterated Fréchet derivatives of norm exp.
lemma norm_iteratedFDeriv_exp (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Real.iter_deriv_exp]
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

-- Tight bound for exp of a continuous linear form (no factorial).
lemma norm_iteratedFDeriv_exp_comp_linear
    (Lin : (Fin 3 → ℝ) →L[ℝ] ℝ) (x : Fin 3 → ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun t => Real.exp (Lin t)) x‖ ≤
      Real.exp (Lin x) * ‖Lin‖ ^ i := by
  have heq : (fun t => Real.exp (Lin t)) = Real.exp ∘ ⇑Lin := rfl
  rw [heq, Lin.iteratedFDeriv_comp_right Real.contDiff_exp x le_top]
  calc ‖(iteratedFDeriv ℝ i Real.exp (Lin x)).compContinuousLinearMap
        fun _ => Lin‖
      ≤ ‖iteratedFDeriv ℝ i Real.exp (Lin x)‖ * ∏ _ : Fin i, ‖Lin‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = Real.exp (Lin x) * ‖Lin‖ ^ i := by
        rw [norm_iteratedFDeriv_exp]
        simp [Finset.prod_const, Finset.card_univ]

lemma norm_proj_le (i : Fin 3) :
    ‖(ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x i

-- Linear forms appearing in the pulled-back arguments.
def l0 : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)
def l1 : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)
def l20 : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)
def l21 : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)
def lm0 : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  -(ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)

@[simp] lemma l0_apply (t : Fin 3 → ℝ) : l0 t = t 0 := rfl
@[simp] lemma l1_apply (t : Fin 3 → ℝ) : l1 t = t 1 := rfl
lemma l20_apply (t : Fin 3 → ℝ) : l20 t = t 2 - t 0 := by
  simp [l20]
lemma l21_apply (t : Fin 3 → ℝ) : l21 t = t 2 - t 1 := by
  simp [l21]
lemma lm0_apply (t : Fin 3 → ℝ) : lm0 t = -(t 0) := by
  simp [lm0]

lemma norm_l0_le : ‖l0‖ ≤ 1 := norm_proj_le 0
lemma norm_l1_le : ‖l1‖ ≤ 1 := norm_proj_le 1
lemma norm_l20_le : ‖l20‖ ≤ 2 := by
  have h2 := norm_proj_le (2 : Fin 3)
  have h0 := norm_proj_le (0 : Fin 3)
  dsimp [l20]
  calc ‖ContinuousLinearMap.proj (2 : Fin 3) -
        ContinuousLinearMap.proj (0 : Fin 3)‖
      ≤ ‖(ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ +
        ‖(ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num
lemma norm_l21_le : ‖l21‖ ≤ 2 := by
  have h2 := norm_proj_le (2 : Fin 3)
  have h1 := norm_proj_le (1 : Fin 3)
  dsimp [l21]
  calc ‖ContinuousLinearMap.proj (2 : Fin 3) -
        ContinuousLinearMap.proj (1 : Fin 3)‖
      ≤ ‖(ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ +
        ‖(ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num
lemma norm_lm0_le : ‖lm0‖ ≤ 1 := by
  have h0 := norm_proj_le (0 : Fin 3)
  dsimp [lm0]
  calc ‖-(ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)‖
      = ‖(ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ := norm_neg _
    _ ≤ 1 := h0

-- Membership in the localizer ball gives a norm bound.
lemma norm_le_of_mem_ball {R : ℝ} {y : Fin 3 → ℝ}
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) : ‖y‖ ≤ R := by
  have h := Metric.mem_closedBall.mp hy
  simpa [dist_eq_norm] using h

-- Coordinate bound on the ball.
lemma abs_coord_le_of_mem_ball {R : ℝ} {y : Fin 3 → ℝ}
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) (i : Fin 3) :
    |y i| ≤ R := by
  have hnorm := norm_le_of_mem_ball hy
  calc |y i| = ‖y i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖y‖ := norm_le_pi_norm y i
    _ ≤ R := hnorm

-- Exponential bounds on the ball.
lemma exp_l0_le_of_mem_ball {R : ℝ} {y : Fin 3 → ℝ}
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
    Real.exp (l0 y) ≤ Real.exp R := by
  apply Real.exp_le_exp.mpr
  have h := abs_coord_le_of_mem_ball hy 0
  have hle : y 0 ≤ R := le_trans (le_abs_self _) h
  simpa [l0] using hle

lemma exp_l1_le_of_mem_ball {R : ℝ} {y : Fin 3 → ℝ}
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
    Real.exp (l1 y) ≤ Real.exp R := by
  apply Real.exp_le_exp.mpr
  have h := abs_coord_le_of_mem_ball hy 1
  have hle : y 1 ≤ R := le_trans (le_abs_self _) h
  simpa [l1] using hle

lemma exp_l20_le_of_mem_ball {R : ℝ} {y : Fin 3 → ℝ} (hR : 0 ≤ R)
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
    Real.exp (l20 y) ≤ Real.exp (2 * R) := by
  apply Real.exp_le_exp.mpr
  have h2 := abs_coord_le_of_mem_ball hy 2
  have h0 := abs_coord_le_of_mem_ball hy 0
  have : y 2 - y 0 ≤ 2 * R := by
    have h2' : y 2 ≤ R := le_trans (le_abs_self _) h2
    have h0' : -(y 0) ≤ R := le_trans (neg_le_abs _) h0
    linarith
  simpa [l20] using this

lemma exp_l21_le_of_mem_ball {R : ℝ} {y : Fin 3 → ℝ}
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
    Real.exp (l21 y) ≤ Real.exp (2 * R) := by
  apply Real.exp_le_exp.mpr
  have h2 := abs_coord_le_of_mem_ball hy 2
  have h1 := abs_coord_le_of_mem_ball hy 1
  have : y 2 - y 1 ≤ 2 * R := by
    have h2' : y 2 ≤ R := le_trans (le_abs_self _) h2
    have h1' : -(y 1) ≤ R := le_trans (neg_le_abs _) h1
    linarith
  simpa [l21] using this

lemma exp_lm0_le_of_mem_ball {R : ℝ} {y : Fin 3 → ℝ}
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
    Real.exp (lm0 y) ≤ Real.exp R := by
  apply Real.exp_le_exp.mpr
  have h0 := abs_coord_le_of_mem_ball hy 0
  have : -(y 0) ≤ R := le_trans (neg_le_abs _) h0
  simpa [lm0] using this

-- Smoothness of exp of linear forms.
lemma contDiff_exp_l0 : ContDiff ℝ ∞ (fun t : Fin 3 → ℝ => Real.exp (l0 t)) :=
  Real.contDiff_exp.comp_continuousLinearMap
lemma contDiff_exp_l1 : ContDiff ℝ ∞ (fun t : Fin 3 → ℝ => Real.exp (l1 t)) :=
  Real.contDiff_exp.comp_continuousLinearMap
lemma contDiff_exp_l20 : ContDiff ℝ ∞ (fun t : Fin 3 → ℝ => Real.exp (l20 t)) :=
  Real.contDiff_exp.comp_continuousLinearMap
lemma contDiff_exp_l21 : ContDiff ℝ ∞ (fun t : Fin 3 → ℝ => Real.exp (l21 t)) :=
  Real.contDiff_exp.comp_continuousLinearMap
lemma contDiff_exp_lm0 : ContDiff ℝ ∞ (fun t : Fin 3 → ℝ => Real.exp (lm0 t)) :=
  Real.contDiff_exp.comp_continuousLinearMap

-- Clean inner maps (exp of linear forms with constant coefficients).
def PhiE (Lpow : ℝ) (k : ℤ) (t : Fin 3 → ℝ) : ℝ :=
  Lpow / (2 * k) * (Real.exp (l1 t) - Real.exp (l0 t))

def PhiN (cN1 cN2 : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  cN1 * (Real.exp (l20 t) - Real.exp (l21 t)) + cN2 * Real.exp (lm0 t)

-- Smoothness of clean inner maps (coefficients are constant in t).
lemma contDiff_PhiE (Lpow : ℝ) (k : ℤ) : ContDiff ℝ ∞ (PhiE Lpow k) := by
  have h : PhiE Lpow k =
      fun t : Fin 3 → ℝ => Lpow / (2 * (k : ℝ)) *
        (Real.exp (l1 t) - Real.exp (l0 t)) := rfl
  rw [h]
  exact contDiff_const.mul (contDiff_exp_l1.sub contDiff_exp_l0)
lemma contDiff_PhiN (cN1 cN2 : ℝ) : ContDiff ℝ ∞ (PhiN cN1 cN2) := by
  have h : PhiN cN1 cN2 = fun t : Fin 3 → ℝ =>
      cN1 * (Real.exp (l20 t) - Real.exp (l21 t)) + cN2 * Real.exp (lm0 t) := rfl
  rw [h]
  exact (contDiff_const.mul (contDiff_exp_l20.sub contDiff_exp_l21)).add
    (contDiff_const.mul contDiff_exp_lm0)

-- Derivative bound for PhiE on the ball (uniform in order).
lemma norm_PhiE_le (Lpow : ℝ) (k : ℤ) (R : ℝ) (y : Fin 3 → ℝ) (i : ℕ)
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
    ‖iteratedFDeriv ℝ i (PhiE Lpow k) y‖ ≤
      ‖Lpow / (2 * (k : ℝ))‖ * (2 * Real.exp R) := by
  have hE1 : ContDiffAt ℝ i (fun t : Fin 3 → ℝ => Real.exp (l1 t)) y :=
    (contDiff_exp_l1.of_le (by simp)).contDiffAt
  have hE0 : ContDiffAt ℝ i (fun t : Fin 3 → ℝ => Real.exp (l0 t)) y :=
    (contDiff_exp_l0.of_le (by simp)).contDiffAt
  have hExp1 : ‖iteratedFDeriv ℝ i (fun t : Fin 3 → ℝ => Real.exp (l1 t)) y‖ ≤
      Real.exp R := by
    calc ‖iteratedFDeriv ℝ i (fun t => Real.exp (l1 t)) y‖
        ≤ Real.exp (l1 y) * ‖l1‖ ^ i :=
          norm_iteratedFDeriv_exp_comp_linear l1 y i
      _ ≤ Real.exp R * 1 := by
          apply mul_le_mul (exp_l1_le_of_mem_ball hy)
            (pow_le_one₀ (norm_nonneg _) norm_l1_le)
            (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
      _ = Real.exp R := mul_one _
  have hExp0 : ‖iteratedFDeriv ℝ i (fun t : Fin 3 → ℝ => Real.exp (l0 t)) y‖ ≤
      Real.exp R := by
    calc ‖iteratedFDeriv ℝ i (fun t => Real.exp (l0 t)) y‖
        ≤ Real.exp (l0 y) * ‖l0‖ ^ i :=
          norm_iteratedFDeriv_exp_comp_linear l0 y i
      _ ≤ Real.exp R * 1 := by
          apply mul_le_mul (exp_l0_le_of_mem_ball hy)
            (pow_le_one₀ (norm_nonneg _) norm_l0_le)
            (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
      _ = Real.exp R := mul_one _
  have hPhiEq : PhiE Lpow k =
      (Lpow / (2 * (k : ℝ))) • ((fun t : Fin 3 → ℝ => Real.exp (l1 t)) -
        (fun t : Fin 3 → ℝ => Real.exp (l0 t))) := by
    funext t
    simp [PhiE, smul_eq_mul, Pi.sub_apply]
  have hSub : ContDiffAt ℝ i ((fun t : Fin 3 → ℝ => Real.exp (l1 t)) -
      (fun t : Fin 3 → ℝ => Real.exp (l0 t))) y := hE1.sub hE0
  rw [hPhiEq, iteratedFDeriv_const_smul_apply hSub,
    iteratedFDeriv_sub_apply hE1 hE0]
  calc ‖(Lpow / (2 * (k : ℝ))) •
        (iteratedFDeriv ℝ i (fun t => Real.exp (l1 t)) y -
          iteratedFDeriv ℝ i (fun t => Real.exp (l0 t)) y)‖
      = ‖Lpow / (2 * (k : ℝ))‖ *
        ‖iteratedFDeriv ℝ i (fun t => Real.exp (l1 t)) y -
          iteratedFDeriv ℝ i (fun t => Real.exp (l0 t)) y‖ := norm_smul _ _
    _ ≤ ‖Lpow / (2 * (k : ℝ))‖ * (Real.exp R + Real.exp R) := by
        gcongr
        calc ‖iteratedFDeriv ℝ i (fun t => Real.exp (l1 t)) y -
              iteratedFDeriv ℝ i (fun t => Real.exp (l0 t)) y‖
            ≤ ‖iteratedFDeriv ℝ i (fun t => Real.exp (l1 t)) y‖ +
              ‖iteratedFDeriv ℝ i (fun t => Real.exp (l0 t)) y‖ := norm_sub_le _ _
          _ ≤ Real.exp R + Real.exp R := add_le_add hExp1 hExp0
    _ = ‖Lpow / (2 * (k : ℝ))‖ * (2 * Real.exp R) := by ring

-- Derivative bound for PhiN on the ball.
-- Gives the form E * Q^i with Q = 2, E depending on coefficients and R.
lemma norm_PhiN_le (cN1 cN2 R : ℝ) (y : Fin 3 → ℝ) (i : ℕ)
    (hR : 0 < R) (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
    ‖iteratedFDeriv ℝ i (PhiN cN1 cN2) y‖ ≤
      ((‖cN1‖ * 2 + ‖cN2‖) * Real.exp (2 * R)) * 2 ^ i := by
  have hE20 : ContDiffAt ℝ i (fun t : Fin 3 → ℝ => Real.exp (l20 t)) y :=
    (contDiff_exp_l20.of_le (by simp)).contDiffAt
  have hE21 : ContDiffAt ℝ i (fun t : Fin 3 → ℝ => Real.exp (l21 t)) y :=
    (contDiff_exp_l21.of_le (by simp)).contDiffAt
  have hEm0 : ContDiffAt ℝ i (fun t : Fin 3 → ℝ => Real.exp (lm0 t)) y :=
    (contDiff_exp_lm0.of_le (by simp)).contDiffAt
  have hRnonneg : 0 ≤ R := hR.le
  have hExpR_le_2R : Real.exp R ≤ Real.exp (2 * R) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hExp20 : ‖iteratedFDeriv ℝ i (fun t : Fin 3 → ℝ => Real.exp (l20 t)) y‖ ≤
      Real.exp (2 * R) * 2 ^ i := by
    calc ‖iteratedFDeriv ℝ i (fun t => Real.exp (l20 t)) y‖
        ≤ Real.exp (l20 y) * ‖l20‖ ^ i :=
          norm_iteratedFDeriv_exp_comp_linear l20 y i
      _ ≤ Real.exp (2 * R) * 2 ^ i := by
          apply mul_le_mul (exp_l20_le_of_mem_ball hRnonneg hy)
            (pow_le_pow_left₀ (norm_nonneg _) norm_l20_le _)
            (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hExp21 : ‖iteratedFDeriv ℝ i (fun t : Fin 3 → ℝ => Real.exp (l21 t)) y‖ ≤
      Real.exp (2 * R) * 2 ^ i := by
    calc ‖iteratedFDeriv ℝ i (fun t => Real.exp (l21 t)) y‖
        ≤ Real.exp (l21 y) * ‖l21‖ ^ i :=
          norm_iteratedFDeriv_exp_comp_linear l21 y i
      _ ≤ Real.exp (2 * R) * 2 ^ i := by
          apply mul_le_mul (exp_l21_le_of_mem_ball hy)
            (pow_le_pow_left₀ (norm_nonneg _) norm_l21_le _)
            (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hExpm0 : ‖iteratedFDeriv ℝ i (fun t : Fin 3 → ℝ => Real.exp (lm0 t)) y‖ ≤
      Real.exp (2 * R) * 2 ^ i := by
    calc ‖iteratedFDeriv ℝ i (fun t => Real.exp (lm0 t)) y‖
        ≤ Real.exp (lm0 y) * ‖lm0‖ ^ i :=
          norm_iteratedFDeriv_exp_comp_linear lm0 y i
      _ ≤ Real.exp R * 1 := by
          apply mul_le_mul (exp_lm0_le_of_mem_ball hy)
            (pow_le_one₀ (norm_nonneg _) norm_lm0_le)
            (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
      _ ≤ Real.exp (2 * R) * 2 ^ i := by
          apply mul_le_mul hExpR_le_2R (one_le_pow₀ (by norm_num))
            zero_le_one (Real.exp_pos _).le
  have hPhiEq : PhiN cN1 cN2 =
      cN1 • ((fun t : Fin 3 → ℝ => Real.exp (l20 t)) -
        (fun t : Fin 3 → ℝ => Real.exp (l21 t))) +
      cN2 • (fun t : Fin 3 → ℝ => Real.exp (lm0 t)) := by
    funext t
    simp [PhiN, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
  have hSub : ContDiffAt ℝ i ((fun t : Fin 3 → ℝ => Real.exp (l20 t)) -
      (fun t : Fin 3 → ℝ => Real.exp (l21 t))) y := hE20.sub hE21
  rw [hPhiEq]
  have hAdd : iteratedFDeriv ℝ i (cN1 •
      ((fun t : Fin 3 → ℝ => Real.exp (l20 t)) -
        (fun t : Fin 3 → ℝ => Real.exp (l21 t))) +
      cN2 • (fun t : Fin 3 → ℝ => Real.exp (lm0 t))) y =
      cN1 • (iteratedFDeriv ℝ i (fun t => Real.exp (l20 t)) y -
        iteratedFDeriv ℝ i (fun t => Real.exp (l21 t)) y) +
      cN2 • iteratedFDeriv ℝ i (fun t => Real.exp (lm0 t)) y := by
    have h1 : ContDiffAt ℝ i (cN1 •
        ((fun t : Fin 3 → ℝ => Real.exp (l20 t)) -
          (fun t : Fin 3 → ℝ => Real.exp (l21 t)))) y :=
      hSub.const_smul cN1
    have h2 : ContDiffAt ℝ i (cN2 •
        (fun t : Fin 3 → ℝ => Real.exp (lm0 t))) y :=
      hEm0.const_smul cN2
    rw [iteratedFDeriv_add_apply h1 h2,
      iteratedFDeriv_const_smul_apply hSub,
      iteratedFDeriv_sub_apply hE20 hE21,
      iteratedFDeriv_const_smul_apply hEm0]
  rw [hAdd]
  calc ‖cN1 • (iteratedFDeriv ℝ i (fun t => Real.exp (l20 t)) y -
        iteratedFDeriv ℝ i (fun t => Real.exp (l21 t)) y) +
      cN2 • iteratedFDeriv ℝ i (fun t => Real.exp (lm0 t)) y‖
      ≤ ‖cN1 • (iteratedFDeriv ℝ i (fun t => Real.exp (l20 t)) y -
          iteratedFDeriv ℝ i (fun t => Real.exp (l21 t)) y)‖ +
        ‖cN2 • iteratedFDeriv ℝ i (fun t => Real.exp (lm0 t)) y‖ :=
        norm_add_le _ _
    _ ≤ (‖cN1‖ * (Real.exp (2 * R) * 2 ^ i + Real.exp (2 * R) * 2 ^ i)) +
        (‖cN2‖ * (Real.exp (2 * R) * 2 ^ i)) := by
        apply add_le_add
        · rw [norm_smul]
          gcongr
          calc ‖iteratedFDeriv ℝ i (fun t => Real.exp (l20 t)) y -
                iteratedFDeriv ℝ i (fun t => Real.exp (l21 t)) y‖
              ≤ ‖iteratedFDeriv ℝ i (fun t => Real.exp (l20 t)) y‖ +
                ‖iteratedFDeriv ℝ i (fun t => Real.exp (l21 t)) y‖ :=
                norm_sub_le _ _
            _ ≤ Real.exp (2 * R) * 2 ^ i + Real.exp (2 * R) * 2 ^ i :=
                add_le_add hExp20 hExp21
        · rw [norm_smul]
          exact mul_le_mul_of_nonneg_left hExpm0 (norm_nonneg _)
    _ = ((‖cN1‖ * 2 + ‖cN2‖) * Real.exp (2 * R)) * 2 ^ i := by ring

-- The original pulled-back arguments equal the clean ones when
-- E = U * L^{-K0} and cN1 = Z/(k*U*V), cN2 = 1/(U*V).
-- Proved by unfolding `pulledCutoff` (its `let`s are definitionally transparent)
-- and field simplifications with exp/U/V/k nonzero.
lemma PhiE_eq (U E Lpow : ℝ) (k : ℤ) (t : Fin 3 → ℝ)
    (_hU : U ≠ 0) (_hk : (k : ℝ) ≠ 0) (_hE : E ≠ 0)
    (hUE : U / (2 * (k : ℝ) * E) = Lpow / (2 * (k : ℝ))) :
    (U * Real.exp (t 1) - U * Real.exp (t 0)) / (2 * (k : ℝ) * E) =
      PhiE Lpow k t := by
  dsimp [PhiE]
  rw [← hUE]
  ring

lemma PhiN_eq (U V Z : ℝ) (k : ℤ) (t : Fin 3 → ℝ)
    (hU : U ≠ 0) (hV : V ≠ 0) (hk : (k : ℝ) ≠ 0) :
    ((U * Real.exp (t 1) - U * Real.exp (t 0)) * (Z * Real.exp (t 2)) /
      ((k : ℝ) * (U * Real.exp (t 0)) * (U * Real.exp (t 1)) * V) +
      1 / ((U * Real.exp (t 0)) * V)) =
      PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V)) t := by
  have he0 : Real.exp (t 0) ≠ 0 := Real.exp_ne_zero _
  have he1 : Real.exp (t 1) ≠ 0 := Real.exp_ne_zero _
  have he2 : Real.exp (t 2) ≠ 0 := Real.exp_ne_zero _
  dsimp [PhiN]
  rw [l20_apply, l21_apply, lm0_apply]
  have hexp20 : Real.exp (t 2 - t 0) = Real.exp (t 2) / Real.exp (t 0) := by
    rw [Real.exp_sub]
  have hexp21 : Real.exp (t 2 - t 1) = Real.exp (t 2) / Real.exp (t 1) := by
    rw [Real.exp_sub]
  have hexpm0 : Real.exp (-(t 0)) = 1 / Real.exp (t 0) := by
    rw [Real.exp_neg, one_div]
  rw [hexp20, hexp21, hexpm0]
  field_simp
  try ring

lemma PhiE_coeff_eq (U x K0 : ℝ) (k : ℤ) (hU : U ≠ 0) (hk : (k : ℝ) ≠ 0)
    (hLpos : 0 < L x) :
    U / (2 * (k : ℝ) * (U * L x ^ (-K0))) = L x ^ K0 / (2 * (k : ℝ)) := by
  have hLne : L x ≠ 0 := ne_of_gt hLpos
  have hpow_ne : L x ^ (-K0) ≠ 0 := (Real.rpow_pos_of_pos hLpos _).ne'
  have hpowK_ne : L x ^ K0 ≠ 0 := (Real.rpow_pos_of_pos hLpos _).ne'
  have hKK : L x ^ K0 * L x ^ (-K0) = 1 := by
    rw [← Real.rpow_add hLpos]
    simp
  have h2k : (2 : ℝ) * (k : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hk
  have h1 : U / (2 * (k : ℝ) * (U * L x ^ (-K0))) =
      1 / (2 * (k : ℝ) * L x ^ (-K0)) := by
    field_simp
  rw [h1]
  have h2 : (1 : ℝ) / (2 * (k : ℝ) * L x ^ (-K0)) =
      L x ^ K0 / (2 * (k : ℝ)) := by
    field_simp
    nlinarith [hKK, sq_nonneg (L x ^ K0), sq_nonneg (L x ^ (-K0)),
      mul_pos (Real.rpow_pos_of_pos hLpos K0) (Real.rpow_pos_of_pos hLpos (-K0))]
  exact h2

lemma pulledCutoff_eq_clean (U V Z x K0 : ℝ) (k : ℤ) (etae etan : ℝ → ℝ)
    (localizer : (Fin 3 → ℝ) → ℝ) (t : Fin 3 → ℝ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hk : k ≠ 0)
    (hLpos : 0 < L x) :
    pulledCutoff U V Z (U * L x ^ (-K0)) k etae etan localizer t =
      ((localizer t *
        etae (PhiE (L x ^ K0) k t) *
        etan (PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V)) t) : ℝ) : ℂ) := by
  have hU0 : U ≠ 0 := by linarith
  have hV0 : V ≠ 0 := by linarith
  have hk0 : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hE0 : U * L x ^ (-K0) ≠ 0 :=
    mul_ne_zero hU0 (Real.rpow_pos_of_pos hLpos _).ne'
  have hCoeff := PhiE_coeff_eq U x K0 k hU0 hk0 hLpos
  have hEarg : (U * Real.exp (t 1) - U * Real.exp (t 0)) /
      (2 * (k : ℝ) * (U * L x ^ (-K0))) = PhiE (L x ^ K0) k t :=
    PhiE_eq U _ _ k t hU0 hk0 hE0 hCoeff
  have hNarg : ((U * Real.exp (t 1) - U * Real.exp (t 0)) *
      (Z * Real.exp (t 2)) /
      ((k : ℝ) * (U * Real.exp (t 0)) * (U * Real.exp (t 1)) * V) +
      1 / ((U * Real.exp (t 0)) * V)) =
      PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V)) t :=
    PhiN_eq U V Z k t hU0 hV0 hk0
  -- Unfold `pulledCutoff`; its `let`s are definitionally the inline form.
  have hUnfold : pulledCutoff U V Z (U * L x ^ (-K0)) k etae etan localizer t =
      Complex.ofReal (localizer t *
        etae ((U * Real.exp (t 1) - U * Real.exp (t 0)) /
          (2 * (k : ℝ) * (U * L x ^ (-K0)))) *
        etan (((U * Real.exp (t 1) - U * Real.exp (t 0)) *
          (Z * Real.exp (t 2)) /
          ((k : ℝ) * (U * Real.exp (t 0)) * (U * Real.exp (t 1)) * V) +
          1 / ((U * Real.exp (t 0)) * V)))) := rfl
  have hClean : (Complex.ofReal (localizer t *
        etae (PhiE (L x ^ K0) k t) *
        etan (PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V)) t)) : ℂ) =
      ((localizer t *
        etae (PhiE (L x ^ K0) k t) *
        etan (PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V)) t) : ℝ) : ℂ) := rfl
  rw [hUnfold, hEarg, hNarg, ← hClean]

-- Integer shift is at least one in absolute value.
lemma one_le_abs_intCast (k : ℤ) (hk : k ≠ 0) : 1 ≤ |(k : ℝ)| := by
  by_contra hcon
  have h : |(k : ℝ)| < 1 := not_le.mp hcon
  have habs_ne : |k| ≠ 0 := fun heq => hk (abs_eq_zero.mp heq)
  have hpos : 0 < |k| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm habs_ne)
  have h1le : 1 ≤ |k| := Int.add_one_le_of_lt hpos
  have h1 : ((|k| : ℤ) : ℝ) < 1 := by
    have hcast : ((|k| : ℤ) : ℝ) = |(k : ℝ)| := Int.cast_abs
    rw [hcast]
    exact h
  have h1' : |k| < 1 := by
    have hcast1 : ((1 : ℤ) : ℝ) = (1 : ℝ) := Int.cast_one
    have hlt : ((|k| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
      rw [hcast1]
      exact h1
    exact_mod_cast hlt
  have hcontra : (1 : ℤ) < 1 := lt_of_le_of_lt h1le h1'
  exact lt_irrefl _ hcontra

-- Coefficient of PhiE is bounded by L^{K0}.
lemma norm_PhiE_coeff_le (x K0 : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hL1 : 1 ≤ L x) :
    ‖L x ^ K0 / (2 * (k : ℝ))‖ ≤ L x ^ K0 := by
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL1
  have hpow_pos : 0 < L x ^ K0 := Real.rpow_pos_of_pos hLpos _
  have hk1 : 1 ≤ |(k : ℝ)| := one_le_abs_intCast k hk
  have h1le : (1 : ℝ) ≤ |(2 : ℝ) * (k : ℝ)| := by
    calc (1 : ℝ) ≤ 2 * 1 := by norm_num
      _ ≤ 2 * |(k : ℝ)| := by gcongr
      _ = |(2 : ℝ) * (k : ℝ)| := by rw [abs_mul]; norm_num
  calc ‖L x ^ K0 / (2 * (k : ℝ))‖
      = (L x ^ K0) / |(2 : ℝ) * (k : ℝ)| := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow_pos]
    _ ≤ (L x ^ K0) / 1 :=
        div_le_div_of_nonneg_left hpow_pos.le zero_lt_one h1le
    _ = L x ^ K0 := div_one _

-- Coefficients of PhiN are bounded by 8 * L^{CZ}.
lemma norm_cN1_le (x U V Z CZ : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUVlow : x / 8 ≤ U * V)
    (hZ : Z ≤ x * L x ^ CZ) (hZpos : 0 < Z) (hxpos : 0 < x)
    (hL1 : 1 ≤ L x) (hCZ : 0 < CZ) :
    ‖Z / ((k : ℝ) * U * V)‖ ≤ 8 * L x ^ CZ := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hUVpos : 0 < U * V := mul_pos hUpos hVpos
  have hk1 : 1 ≤ |(k : ℝ)| := one_le_abs_intCast k hk
  have hk0 : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hkuv_ne : (k : ℝ) * U * V ≠ 0 :=
    mul_ne_zero (mul_ne_zero hk0 hUpos.ne') hVpos.ne'
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL1
  have hpow_pos : 0 < L x ^ CZ := Real.rpow_pos_of_pos hLpos _
  have hZUV : Z / (U * V) ≤ 8 * L x ^ CZ := by
    have hx8pos : 0 < x / 8 := by linarith
    have hxcpos : 0 < x * L x ^ CZ := mul_pos hxpos hpow_pos
    have h1 : Z / (U * V) ≤ (x * L x ^ CZ) / (x / 8) :=
      div_le_div₀ hxcpos.le hZ hx8pos hUVlow
    have h2 : (x * L x ^ CZ) / (x / 8) = 8 * L x ^ CZ := by
      field_simp
    rw [h2] at h1
    exact h1
  have hleUV : U * V ≤ |(k : ℝ)| * (U * V) := by
    calc U * V = 1 * (U * V) := (one_mul _).symm
      _ ≤ |(k : ℝ)| * (U * V) := by gcongr
  calc ‖Z / ((k : ℝ) * U * V)‖
      = Z / (|(k : ℝ)| * (U * V)) := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hZpos]
        congr 1
        rw [abs_mul, abs_mul, abs_of_pos hUpos, abs_of_pos hVpos]
        ring
    _ ≤ Z / (U * V) :=
        div_le_div_of_nonneg_left hZpos.le hUVpos hleUV
    _ ≤ 8 * L x ^ CZ := hZUV

-- Second PhiN coefficient is also bounded by 8 * L^{CZ} (using L^{CZ} ≥ 1, x ≥ 1).
lemma norm_cN2_le (x U V CZ : ℝ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUVlow : x / 8 ≤ U * V)
    (hx1 : 1 ≤ x) (hL1 : 1 ≤ L x) (hCZ : 0 ≤ CZ) :
    ‖(1 : ℝ) / (U * V)‖ ≤ 8 * L x ^ CZ := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hUVpos : 0 < U * V := mul_pos hUpos hVpos
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL1
  have hpow_ge1 : 1 ≤ L x ^ CZ := Real.one_le_rpow hL1 hCZ
  have h1 : (1 : ℝ) / (U * V) ≤ 8 / x := by
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hx8pos : 0 < x / 8 := by linarith
    have hle : (1 : ℝ) / (U * V) ≤ 1 / (x / 8) :=
      one_div_le_one_div_of_le hx8pos hUVlow
    -- 1/(x/8) = 8/x
    have heq : (1 : ℝ) / (x / 8) = 8 / x := by field_simp
    rw [heq] at hle
    exact hle
  have h2 : 8 / x ≤ 8 := by
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    rw [div_le_iff₀ hxpos]
    calc (8 : ℝ) = 8 * 1 := (mul_one _).symm
      _ ≤ 8 * x := by gcongr
  calc ‖(1 : ℝ) / (U * V)‖
      = 1 / (U * V) := by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hUVpos)]
    _ ≤ 8 := le_trans h1 h2
    _ ≤ 8 * L x ^ CZ := by
        calc (8 : ℝ) = 8 * 1 := (mul_one _).symm
          _ ≤ 8 * L x ^ CZ := by gcongr

-- Nat pow of rpow equals rpow of product (for L > 0).
lemma rpow_nat_pow (L K : ℝ) (hLpos : 0 < L) (n : ℕ) :
    (L ^ K) ^ n = L ^ (K * (n : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hLpos)]

-- Max of bounds up to n (as a sum, dominating each term).
def Bmax (bounds : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), bounds i

lemma Bmax_nonneg (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) (n : ℕ) :
    0 ≤ Bmax bounds n := by
  dsimp [Bmax]
  exact Finset.sum_nonneg (fun i _ => hb i)

lemma bounds_le_Bmax (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j)
    {n i : ℕ} (hi : i ≤ n) : bounds i ≤ Bmax bounds n := by
  dsimp [Bmax]
  apply Finset.single_le_sum (fun j _ => hb j)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi)

-- Upgrade a derivative bound from exponent P to larger P'.
lemma upgrade_exp_bound {B : ℕ → ℝ} {P P' : ℝ} {Lpow : ℝ}
    (hBnonneg : ∀ i, 0 ≤ B i) (hL1 : 1 ≤ Lpow)
    (hPle : P ≤ P') :
    ∀ i, B i * Lpow ^ (P * ((i : ℝ) + 1)) ≤ B i * Lpow ^ (P' * ((i : ℝ) + 1)) := by
  intro i
  apply mul_le_mul_of_nonneg_left _ (hBnonneg i)
  apply Real.rpow_le_rpow_of_exponent_le hL1
  apply mul_le_mul_of_nonneg_right hPle (by positivity)

-- Product of two functions with same exponent P gives exponent 2*P.
-- Coefficients combine via binomial sums; L-powers factor out using L ≥ 1.
lemma norm_prod_le_of_bounds {f g : (Fin 3 → ℝ) → ℝ}
    {Bf Bg : ℕ → ℝ} {P Lpow : ℝ} {y : Fin 3 → ℝ} {n : ℕ}
    (hf : ContDiff ℝ (n : ℕ∞) f) (hg : ContDiff ℝ (n : ℕ∞) g)
    (hBfnonneg : ∀ i, 0 ≤ Bf i) (hBgnonneg : ∀ i, 0 ≤ Bg i)
    (hPnonneg : 0 ≤ P) (hL1 : 1 ≤ Lpow) (hLpos : 0 < Lpow)
    (hfB : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i f y‖ ≤ Bf i * Lpow ^ (P * ((i : ℝ) + 1)))
    (hgB : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g y‖ ≤ Bg i * Lpow ^ (P * ((i : ℝ) + 1))) :
    ‖iteratedFDeriv ℝ n (fun t => f t * g t) y‖ ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * Bf i * Bg (n - i)) *
        Lpow ^ (2 * P * ((n : ℝ) + 1)) := by
  have hbase := norm_iteratedFDeriv_mul_le hf hg y (le_refl _)
  -- Each summand is bounded by coefficient times final L-power.
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (n - i) g y‖ ≤
      ((n.choose i : ℝ) * Bf i * Bg (n - i)) *
        Lpow ^ (2 * P * ((n : ℝ) + 1)) := by
    intro i hi
    have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hni_le : n - i ≤ n := Nat.sub_le n i
    have hfi := hfB i hi_le
    have hgi := hgB (n - i) hni_le
    have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    have hBf_nonneg : 0 ≤ Bf i := hBfnonneg i
    have hBg_nonneg : 0 ≤ Bg (n - i) := hBgnonneg _
    have hLpow_exp : Lpow ^ (P * ((i : ℝ) + 1)) * Lpow ^ (P * (((n - i : ℕ) : ℝ) + 1)) ≤
        Lpow ^ (2 * P * ((n : ℝ) + 1)) := by
      have hexp_le : P * ((i : ℝ) + 1) + P * (((n - i : ℕ) : ℝ) + 1) ≤
          2 * P * ((n : ℝ) + 1) := by
        -- P*(i+1) + P*(n-i+1) = P*(i + (n-i) + 2) ≤ P*(n+1+2?) ...
        -- Actually P*(i+1)+P*(n-i+1) = P*(i + (n-i) + 2) ≤ P*(n+1+2)? Hmm need ≤2*P*(n+1).
        -- Since i + (n-i) ≤ n+? Actually i + (n-i) = n (as reals, when i≤n).
        -- So sum = P*(n+2) ≤ 2*P*(n+1) because P*n ≥ 0.
        have hsum_eq : P * ((i : ℝ) + 1) + P * (((n - i : ℕ) : ℝ) + 1) =
            P * (((i : ℝ) + ((n - i : ℕ) : ℝ)) + 2) := by ring
        have hn_eq2 : (i : ℝ) + ((n - i : ℕ) : ℝ) = (n : ℝ) := by
          calc (i : ℝ) + ((n - i : ℕ) : ℝ) = ((i + (n - i) : ℕ) : ℝ) :=
                (Nat.cast_add _ _).symm
            _ = (n : ℝ) := by rw [Nat.add_sub_of_le hi_le]
        rw [hsum_eq, hn_eq2]
        -- Need P*(n+2) ≤ 2*P*(n+1): since P*n ≥ 0.
        have hPn_nonneg : 0 ≤ P * (n : ℝ) := mul_nonneg hPnonneg (Nat.cast_nonneg _)
        nlinarith
      calc Lpow ^ (P * ((i : ℝ) + 1)) * Lpow ^ (P * (((n - i : ℕ) : ℝ) + 1))
          = Lpow ^ (P * ((i : ℝ) + 1) + P * (((n - i : ℕ) : ℝ) + 1)) := by
            rw [← Real.rpow_add hLpos]
        _ ≤ Lpow ^ (2 * P * ((n : ℝ) + 1)) :=
            Real.rpow_le_rpow_of_exponent_le hL1 hexp_le
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) g y‖
        ≤ (n.choose i : ℝ) * (Bf i * Lpow ^ (P * ((i : ℝ) + 1))) *
          (Bg (n - i) * Lpow ^ (P * (((n - i : ℕ) : ℝ) + 1))) := by
          gcongr
        _ = ((n.choose i : ℝ) * Bf i * Bg (n - i)) *
          (Lpow ^ (P * ((i : ℝ) + 1)) * Lpow ^ (P * (((n - i : ℕ) : ℝ) + 1))) := by
          ring
        _ ≤ ((n.choose i : ℝ) * Bf i * Bg (n - i)) *
          Lpow ^ (2 * P * ((n : ℝ) + 1)) := by gcongr
  calc ‖iteratedFDeriv ℝ n (fun t => f t * g t) y‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f y‖ * ‖iteratedFDeriv ℝ (n - i) g y‖ := hbase
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (((n.choose i : ℝ) * Bf i * Bg (n - i)) *
          Lpow ^ (2 * P * ((n : ℝ) + 1))) :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * Bf i * Bg (n - i)) *
        Lpow ^ (2 * P * ((n : ℝ) + 1)) := by
        rw [Finset.sum_mul]

-- Outer composition bound for etae ∘ PhiE on the ball.
-- Uses `norm_iteratedFDeriv_comp_le` with uniform outer C_n and inner D^i.
lemma norm_Ge_le (bounds : ℕ → ℝ) (x C K0 R Lpow : ℝ) (k : ℤ)
    (etae : ℝ → ℝ) (y : Fin 3 → ℝ) (n : ℕ)
    (hC : 0 < C) (hK0 : 0 < K0) (hR : 0 < R)
    (hb : ∀ j, 0 ≤ bounds j)
    (hL1 : 1 ≤ L x) (hk : k ≠ 0)
    (hLpow_eq : Lpow = L x ^ K0)
    (hLpow_pos : 0 < Lpow)
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R)
    (hetae : ContDiff ℝ ∞ etae)
    (hDeriv : ∀ j y, ‖iteratedDeriv j etae y‖ ≤ bounds j * L x ^ (C * (j + 1))) :
    ‖iteratedFDeriv ℝ n (etae ∘ PhiE Lpow k) y‖ ≤
      (n.factorial : ℝ) * (Bmax bounds n * L x ^ (C * (n + 1))) *
        (2 * Real.exp R * L x ^ K0) ^ n := by
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL1
  have hpowK_pos : 0 < L x ^ K0 := Real.rpow_pos_of_pos hLpos _
  have hpowK_ge1 : 1 ≤ L x ^ K0 := Real.one_le_rpow hL1 hK0.le
  have hexp_ge1 : 1 ≤ Real.exp R := Real.one_le_exp hR.le
  have hD_ge1 : 1 ≤ 2 * Real.exp R * L x ^ K0 := by
    calc (1 : ℝ) ≤ 2 * 1 * 1 := by norm_num
      _ ≤ 2 * Real.exp R * L x ^ K0 := by gcongr
  -- Outer uniform bound C_n.
  have hCbound : ∀ i, i ≤ n →
      ‖iteratedFDeriv ℝ i etae (PhiE Lpow k y)‖ ≤
        Bmax bounds n * L x ^ (C * (n + 1)) := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    calc ‖iteratedDeriv i etae (PhiE Lpow k y)‖
        ≤ bounds i * L x ^ (C * (i + 1)) := hDeriv i _
      _ ≤ Bmax bounds n * L x ^ (C * (n + 1)) := by
          apply mul_le_mul (bounds_le_Bmax bounds hb hi)
            (Real.rpow_le_rpow_of_exponent_le hL1 ?_)
            (Real.rpow_nonneg (le_trans zero_le_one hL1) _) (Bmax_nonneg bounds hb n)
          -- C*(i+1) ≤ C*(n+1)
          have hi' : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hi
          have hi1 : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
          have hCexp : C * ((i : ℝ) + 1) ≤ C * ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hi1 hC.le
          -- need to match C*(↑i+1) vs C*(↑(i+1))? Elaborator uses ↑i+1 or ↑(i+1)?
          -- `C * (j+1)` in task elaborates to `C * (↑j + 1)`; our goal has same.
          simpa using hCexp
  -- Inner exponential bound D^i.
  have hDbound : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (PhiE Lpow k) y‖ ≤
        (2 * Real.exp R * L x ^ K0) ^ i := by
    intro i hi1 _hi2
    have hPhi : ‖iteratedFDeriv ℝ i (PhiE Lpow k) y‖ ≤
        ‖Lpow / (2 * (k : ℝ))‖ * (2 * Real.exp R) :=
      norm_PhiE_le Lpow k R y i hy
    have hCoeff : ‖Lpow / (2 * (k : ℝ))‖ ≤ L x ^ K0 := by
      rw [hLpow_eq]
      exact norm_PhiE_coeff_le x K0 k hk hL1
    have hUpper : ‖iteratedFDeriv ℝ i (PhiE Lpow k) y‖ ≤
        2 * Real.exp R * L x ^ K0 := by
      calc ‖iteratedFDeriv ℝ i (PhiE Lpow k) y‖
          ≤ ‖Lpow / (2 * (k : ℝ))‖ * (2 * Real.exp R) := hPhi
        _ ≤ L x ^ K0 * (2 * Real.exp R) :=
            mul_le_mul_of_nonneg_right hCoeff (by positivity)
        _ = 2 * Real.exp R * L x ^ K0 := by ring
    calc ‖iteratedFDeriv ℝ i (PhiE Lpow k) y‖
        ≤ 2 * Real.exp R * L x ^ K0 := hUpper
      _ ≤ (2 * Real.exp R * L x ^ K0) ^ i :=
          le_self_pow₀ hD_ge1 (by omega : i ≠ 0)
  exact norm_iteratedFDeriv_comp_le hetae (contDiff_PhiE Lpow k) (by simp) y
    hCbound hDbound

-- Outer composition bound for etan ∘ PhiN on the ball.
lemma norm_Gn_le (bounds : ℕ → ℝ) (x C CZ R : ℝ) (U V Z : ℝ) (k : ℤ)
    (etan : ℝ → ℝ) (y : Fin 3 → ℝ) (n : ℕ)
    (hC : 0 < C) (hCZ : 0 < CZ) (hR : 0 < R)
    (hb : ∀ j, 0 ≤ bounds j)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUVlow : x / 8 ≤ U * V)
    (hZ : Z ≤ x * L x ^ CZ) (hZpos : 0 < Z)
    (hx1 : 1 ≤ x) (hL1 : 1 ≤ L x)
    (hk : k ≠ 0)
    (hy : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R)
    (hetan : ContDiff ℝ ∞ etan)
    (hDeriv : ∀ j y, ‖iteratedDeriv j etan y‖ ≤ bounds j * L x ^ (C * (j + 1))) :
    ‖iteratedFDeriv ℝ n
      (etan ∘ PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V))) y‖ ≤
      (n.factorial : ℝ) * (Bmax bounds n * L x ^ (C * (n + 1))) *
        (48 * Real.exp (2 * R) * L x ^ CZ) ^ n := by
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL1
  have hpowCZ_pos : 0 < L x ^ CZ := Real.rpow_pos_of_pos hLpos _
  have hpowCZ_ge1 : 1 ≤ L x ^ CZ := Real.one_le_rpow hL1 hCZ.le
  have hexp2R_ge1 : 1 ≤ Real.exp (2 * R) := Real.one_le_exp (by linarith : 0 ≤ 2 * R)
  have hEupper_ge1 : 1 ≤ 24 * L x ^ CZ * Real.exp (2 * R) := by
    calc (1 : ℝ) ≤ 24 * 1 * 1 := by norm_num
      _ ≤ 24 * L x ^ CZ * Real.exp (2 * R) := by gcongr
  have hD_ge1 : 1 ≤ 48 * Real.exp (2 * R) * L x ^ CZ := by
    calc (1 : ℝ) ≤ 48 * 1 * 1 := by norm_num
      _ ≤ 48 * Real.exp (2 * R) * L x ^ CZ := by gcongr
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  -- Outer uniform bound.
  have hCbound : ∀ i, i ≤ n →
      ‖iteratedFDeriv ℝ i etan (PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V)) y)‖ ≤
        Bmax bounds n * L x ^ (C * (n + 1)) := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    calc ‖iteratedDeriv i etan _‖
        ≤ bounds i * L x ^ (C * (i + 1)) := hDeriv i _
      _ ≤ Bmax bounds n * L x ^ (C * (n + 1)) := by
          apply mul_le_mul (bounds_le_Bmax bounds hb hi)
            (Real.rpow_le_rpow_of_exponent_le hL1 ?_)
            (Real.rpow_nonneg (le_trans zero_le_one hL1) _) (Bmax_nonneg bounds hb n)
          have hi' : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hi
          have hi1 : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
          have hCexp : C * ((i : ℝ) + 1) ≤ C * ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hi1 hC.le
          simpa using hCexp
  -- Inner bound with upper coefficients.
  have hcN1 : ‖Z / ((k : ℝ) * U * V)‖ ≤ 8 * L x ^ CZ :=
    norm_cN1_le x U V Z CZ k hk hU hV hUVlow hZ hZpos hxpos hL1 hCZ
  have hcN2 : ‖(1 : ℝ) / (U * V)‖ ≤ 8 * L x ^ CZ :=
    norm_cN2_le x U V CZ hU hV hUVlow hx1 hL1 hCZ.le
  have hDbound : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V))) y‖ ≤
        (48 * Real.exp (2 * R) * L x ^ CZ) ^ i := by
    intro i hi1 _hi2
    have hPhi : ‖iteratedFDeriv ℝ i
          (PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V))) y‖ ≤
          ((‖Z / ((k : ℝ) * U * V)‖ * 2 + ‖(1 : ℝ) / (U * V)‖) *
            Real.exp (2 * R)) * 2 ^ i :=
      norm_PhiN_le _ _ R y i hR hy
    have hEupper : ((‖Z / ((k : ℝ) * U * V)‖ * 2 + ‖(1 : ℝ) / (U * V)‖) *
        Real.exp (2 * R)) ≤ 24 * L x ^ CZ * Real.exp (2 * R) := by
      have h1 : ‖Z / ((k : ℝ) * U * V)‖ * 2 + ‖(1 : ℝ) / (U * V)‖ ≤
          8 * L x ^ CZ * 2 + 8 * L x ^ CZ := by gcongr
      calc ((‖Z / ((k : ℝ) * U * V)‖ * 2 + ‖(1 : ℝ) / (U * V)‖) *
          Real.exp (2 * R))
          ≤ (8 * L x ^ CZ * 2 + 8 * L x ^ CZ) * Real.exp (2 * R) := by gcongr
        _ = 24 * L x ^ CZ * Real.exp (2 * R) := by ring
    have hUpper : ‖iteratedFDeriv ℝ i
          (PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V))) y‖ ≤
          24 * L x ^ CZ * Real.exp (2 * R) * 2 ^ i := by
      calc ‖iteratedFDeriv ℝ i _ y‖
          ≤ ((‖Z / ((k : ℝ) * U * V)‖ * 2 + ‖(1 : ℝ) / (U * V)‖) *
            Real.exp (2 * R)) * 2 ^ i := hPhi
        _ ≤ (24 * L x ^ CZ * Real.exp (2 * R)) * 2 ^ i := by gcongr
    calc ‖iteratedFDeriv ℝ i _ y‖
        ≤ (24 * L x ^ CZ * Real.exp (2 * R)) * 2 ^ i := hUpper
      _ ≤ (24 * L x ^ CZ * Real.exp (2 * R)) ^ i * 2 ^ i :=
          mul_le_mul_of_nonneg_right
            (le_self_pow₀ hEupper_ge1 (by omega : i ≠ 0))
            (pow_nonneg (by norm_num) _)
      _ = (48 * Real.exp (2 * R) * L x ^ CZ) ^ i := by
          have hDE : (48 : ℝ) * Real.exp (2 * R) * L x ^ CZ =
              (24 * L x ^ CZ * Real.exp (2 * R)) * 2 := by ring
          rw [hDE]
          exact (mul_pow _ _ _).symm
  exact norm_iteratedFDeriv_comp_le hetan
    (contDiff_PhiN _ _) (by simp) y hCbound hDbound

theorem PulledCutoffSeparationTask_proof : PulledCutoffSeparationTask := by
  intro hClass C K0 CZ R bounds localBounds localizer hC hK0 hCZ hR hb hLoc hSupp hLocDeriv
  have hSep := hClass.separation
  -- Fixed exponents: P0 = C+K0+CZ, C1 = 4*P0 (two doublings for two products).
  set P0 : ℝ := C + K0 + CZ with hP0
  have hP0pos : 0 < P0 := by linarith
  set C1 : ℝ := 4 * P0 with hC1def
  have hC1pos : 0 < C1 := by linarith
  -- Coefficient bounds for the three factors (all with exponent P0).
  -- BGe/BGn from outer compositions, BLoc = localBounds.
  set BGe : ℕ → ℝ := fun n =>
    (n.factorial : ℝ) * Bmax bounds n * (2 * Real.exp R) ^ n with hBGe
  set BGn : ℕ → ℝ := fun n =>
    (n.factorial : ℝ) * Bmax bounds n * (48 * Real.exp (2 * R)) ^ n with hBGn
  -- bounds1 for F = H*Gn with 4*P0 = C1, inline double sum (no BH name to avoid unfolding).
  -- Inner sum for H_i is ∑ k∈range(i+1), C(i,k)*localBounds_k*BGe_{i-k} (same as hHAll explicit).
  set bounds1 : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * localBounds k * BGe (i - k)) *
      BGn (n - i) with hbounds1
  have hBmaxnonneg : ∀ n, 0 ≤ Bmax bounds n := fun n => Bmax_nonneg bounds (fun j => (hb j).1) n
  have hBGenonneg : ∀ i, 0 ≤ BGe i := by
    intro i
    dsimp [BGe]
    apply mul_nonneg
    · apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact hBmaxnonneg i
    · exact pow_nonneg (by positivity) _
  have hBGnnonneg : ∀ i, 0 ≤ BGn i := by
    intro i
    dsimp [BGn]
    apply mul_nonneg
    · apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact hBmaxnonneg i
    · exact pow_nonneg (by positivity) _
  have hbounds1nonneg : ∀ i, 0 ≤ bounds1 i := by
    intro i
    dsimp [bounds1]
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg
    · apply mul_nonneg
      · exact Nat.cast_nonneg _
      · apply Finset.sum_nonneg
        intro k _
        apply mul_nonneg
        · apply mul_nonneg
          · exact Nat.cast_nonneg _
          · exact (hb k).2
        · exact hBGenonneg _
    · exact hBGnnonneg _
  -- Apply Fourier separation with b = 3, C1, R, bounds1.
  -- hSep gives C1 < Cf; task needs 0 < Cf (from 0 < C1 < Cf).
  obtain ⟨Cf, K, hCf_lt, hKpos, hFourier⟩ :=
    hSep 3 C1 R hC1pos hR bounds1 hbounds1nonneg
  have hCfpos : 0 < Cf := lt_trans hC1pos hCf_lt
  refine ⟨Cf, K, hCfpos, hKpos, ?_⟩
  intro A hA
  obtain ⟨KA, hKApos, hEv⟩ := hFourier A hA
  refine ⟨KA, hKApos, ?_⟩
  -- Eventual largeness: 1 ≤ x and 1 ≤ L x (hence 0 < x, 0 < L x).
  have hEv_x1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hEv_L1 : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := by
    have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
    simpa [L] using hlog
  filter_upwards [hEv, hEv_x1, hEv_L1] with x hxF hx1 hL1
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL1
  intro U V Z k etae etan hU hV hUVlow hUVhigh hZpos hZle hk hetae hetan hDeriv
  -- Define F as the pulled-back cutoff (original form) for this x.
  set F : (Fin 3 → ℝ) → ℂ :=
    fun t => pulledCutoff U V Z (U * L x ^ (-K0)) k etae etan localizer t with hFdef
  -- Clean real and complex versions.
  set cE : ℝ := L x ^ K0 / (2 * (k : ℝ)) with hcE
  set cN1 : ℝ := Z / ((k : ℝ) * U * V) with hcN1
  set cN2 : ℝ := 1 / (U * V) with hcN2
  set Ge : (Fin 3 → ℝ) → ℝ := etae ∘ PhiE (L x ^ K0) k with hGe
  set Gn : (Fin 3 → ℝ) → ℝ := etan ∘ PhiN cN1 cN2 with hGn
  set FR : (Fin 3 → ℝ) → ℝ := fun t => localizer t * Ge t * Gn t with hFR
  set Fclean : (Fin 3 → ℝ) → ℂ := fun t => ((FR t : ℝ) : ℂ) with hFclean
  have hFeq : F = Fclean := by
    funext t
    dsimp [F, Fclean, FR, Ge, Gn]
    exact pulledCutoff_eq_clean U V Z x K0 k etae etan localizer t hU hV hk hLpos
  have hGeCont : ContDiff ℝ ∞ Ge := hetae.comp (contDiff_PhiE _ _)
  have hGnCont : ContDiff ℝ ∞ Gn := hetan.comp (contDiff_PhiN _ _)
  have hFRCont : ContDiff ℝ ∞ FR := (hLoc.mul hGeCont).mul hGnCont
  have hCleanCont : ContDiff ℝ ∞ Fclean := by
    have hEq : Fclean = Complex.ofRealCLM ∘ FR := by
      funext t
      simp [hFclean, hFR]
    rw [hEq]
    exact Complex.ofRealCLM.contDiff.comp hFRCont
  have hCleanSupp : Function.support Fclean ⊆ Metric.closedBall 0 R := by
    intro t ht
    have hLocMem : t ∈ Function.support localizer := by
      simp only [Function.mem_support] at ht ⊢
      intro hEq
      apply ht
      simp [hFclean, hFR, hGe, hGn, hEq]
    exact hSupp hLocMem
  have hP0pos : 0 < P0 := by simp [hP0]; linarith
  have hC1pos2 : 0 < C1 := hC1pos
  have hLpos2 : 0 < L x := hLpos
  have hL1_2 : 1 ≤ L x := hL1
  have hTsupportSub : tsupport Fclean ⊆ Metric.closedBall 0 R :=
    closure_minimal hCleanSupp Metric.isClosed_closedBall
  have hP0eq : P0 = C + K0 + CZ := hP0
  have hC1eq : C1 = 4 * P0 := hC1def
  have hP0nonneg : 0 ≤ P0 := hP0pos.le
  have hCleanBound : ∀ j y, ‖iteratedFDeriv ℝ j Fclean y‖ ≤ bounds1 j * L x ^ (C1 * (j + 1)) := by
    intro j y
    by_cases hyBall : y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R
    · -- Inside the ball: combine Loc, Ge, Gn via two products.
      -- Per-factor bounds with P0.
      have hLocP0 : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i localizer y‖ ≤
          localBounds i * L x ^ (P0 * ((i : ℝ) + 1)) := by
        intro i _
        calc ‖iteratedFDeriv ℝ i localizer y‖ ≤ localBounds i := hLocDeriv i y
          _ = localBounds i * 1 := (mul_one _).symm
          _ ≤ localBounds i * L x ^ (P0 * ((i : ℝ) + 1)) := by
            gcongr
            · exact (hb i).2
            · exact Real.one_le_rpow hL1 (by positivity)
      -- Ge with P0 (from norm_Ge_le + exponent upgrade C*(i+1)+K0*i ≤ P0*(i+1)).
      have hGeP0 : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i Ge y‖ ≤
          BGe i * L x ^ (P0 * ((i : ℝ) + 1)) := by
        intro i hi
        have hGeEq : Ge = etae ∘ PhiE (L x ^ K0) k := hGe
        have hLpowEq : L x ^ K0 = L x ^ K0 := rfl
        have hBase := norm_Ge_le bounds x C K0 R (L x ^ K0) k etae y i
          hC hK0 hR (fun j => (hb j).1) hL1 hk rfl
          (Real.rpow_pos_of_pos hLpos _) hyBall hetae (fun j y => (hDeriv j y).1)
        -- hBase : ‖D^i (etae ∘ PhiE ...)‖ ≤ i! * (Bmax*L^{C*(i+1)}) * (2*exp(R)*L^{K0})^i
        -- Need to rewrite Ge to ... and BGe unfolding + exponent upgrade to P0.
        rw [hGeEq]
        simp only [hBGe]
        -- hBase gives i!*(Bmax*L^{C*(i+1)})*D_e^i with D_e = 2*exp(R)*L^{K0}.
        -- Rewrite D_e^i and combine L-powers, then upgrade exponent to P0.
        have hBGe_nonneg : 0 ≤ (i.factorial : ℝ) * Bmax bounds i * (2 * Real.exp R) ^ i := by
          have h0 := hBGenonneg i
          simpa [hBGe] using h0
        -- Upgrade L-exponent from C*(i+1)+K0*i to P0*(i+1).
        have hexp_le : C * ((i : ℝ) + 1) + K0 * (i : ℝ) ≤ P0 * ((i : ℝ) + 1) := by
          simp only [hP0]
          have hi_nonneg : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
          nlinarith [hC, hK0, hCZ, hi_nonneg]
        have hLpow_eq : L x ^ (C * ((i : ℝ) + 1)) * L x ^ (K0 * (i : ℝ)) =
            L x ^ (C * ((i : ℝ) + 1) + K0 * (i : ℝ)) := by
          rw [← Real.rpow_add hLpos]
        have hLpow_le : L x ^ (C * ((i : ℝ) + 1) + K0 * (i : ℝ)) ≤
            L x ^ (P0 * ((i : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hL1 hexp_le
        -- Rewrite hBase D_e^i and combine.
        have hDe_eq : (2 * Real.exp R * L x ^ K0) ^ i =
            (2 * Real.exp R) ^ i * L x ^ (K0 * (i : ℝ)) := by
          have h1 : (2 * Real.exp R * L x ^ K0) =
              (2 * Real.exp R) * L x ^ K0 := by ring
          rw [h1, mul_pow, rpow_nat_pow _ _ hLpos i]
        calc ‖iteratedFDeriv ℝ i (etae ∘ PhiE (L x ^ K0) k) y‖
            ≤ (i.factorial : ℝ) * (Bmax bounds i * L x ^ (C * ((i : ℝ) + 1))) *
              (2 * Real.exp R * L x ^ K0) ^ i := hBase
          _ = ((i.factorial : ℝ) * Bmax bounds i * (2 * Real.exp R) ^ i) *
              (L x ^ (C * ((i : ℝ) + 1)) * L x ^ (K0 * (i : ℝ))) := by
              rw [hDe_eq]
              ring
          _ = ((i.factorial : ℝ) * Bmax bounds i * (2 * Real.exp R) ^ i) *
              L x ^ (C * ((i : ℝ) + 1) + K0 * (i : ℝ)) := by
              rw [hLpow_eq]
          _ ≤ ((i.factorial : ℝ) * Bmax bounds i * (2 * Real.exp R) ^ i) *
              L x ^ (P0 * ((i : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left hLpow_le hBGe_nonneg
      -- Gn with P0 (from norm_Gn_le + exponent upgrade).
      have hGnP0 : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i Gn y‖ ≤
          BGn i * L x ^ (P0 * ((i : ℝ) + 1)) := by
        intro i hi
        have hGnEq : Gn = etan ∘ PhiN (Z / ((k : ℝ) * U * V)) (1 / (U * V)) := by
          simp [hGn, hcN1, hcN2]
        have hBase := norm_Gn_le bounds x C CZ R U V Z k etan y i
          hC hCZ hR (fun j => (hb j).1) hU hV hUVlow hZle hZpos hx1 hL1 hk hyBall hetan
          (fun j y => (hDeriv j y).2)
        rw [hGnEq]
        simp only [hBGn]
        -- hBase : ‖...‖ ≤ i!*(Bmax*L^{C...})*(48*exp*L^{CZ})^i, upgrade to P0.
        have hBGn_nonneg : 0 ≤ (i.factorial : ℝ) * Bmax bounds i * (48 * Real.exp (2 * R)) ^ i := by
          have h0 := hBGnnonneg i
          simpa [hBGn] using h0
        have hexp_le : C * ((i : ℝ) + 1) + CZ * (i : ℝ) ≤ P0 * ((i : ℝ) + 1) := by
          simp only [hP0]
          have hi_nonneg : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
          nlinarith [hC, hK0, hCZ, hi_nonneg]
        have hLpow_eq : L x ^ (C * ((i : ℝ) + 1)) * L x ^ (CZ * (i : ℝ)) =
            L x ^ (C * ((i : ℝ) + 1) + CZ * (i : ℝ)) := by
          rw [← Real.rpow_add hLpos]
        have hLpow_le : L x ^ (C * ((i : ℝ) + 1) + CZ * (i : ℝ)) ≤
            L x ^ (P0 * ((i : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hL1 hexp_le
        have hDe_eq : (48 * Real.exp (2 * R) * L x ^ CZ) ^ i =
            (48 * Real.exp (2 * R)) ^ i * L x ^ (CZ * (i : ℝ)) := by
          have h1 : (48 * Real.exp (2 * R) * L x ^ CZ) =
              (48 * Real.exp (2 * R)) * L x ^ CZ := by ring
          rw [h1, mul_pow, rpow_nat_pow _ _ hLpos i]
        calc ‖iteratedFDeriv ℝ i (etan ∘ PhiN (Z / (↑k * U * V)) (1 / (U * V))) y‖
            ≤ (i.factorial : ℝ) * (Bmax bounds i * L x ^ (C * ((i : ℝ) + 1))) *
              (48 * Real.exp (2 * R) * L x ^ CZ) ^ i := hBase
          _ = ((i.factorial : ℝ) * Bmax bounds i * (48 * Real.exp (2 * R)) ^ i) *
              (L x ^ (C * ((i : ℝ) + 1)) * L x ^ (CZ * (i : ℝ))) := by
              rw [hDe_eq]
              ring
          _ = ((i.factorial : ℝ) * Bmax bounds i * (48 * Real.exp (2 * R)) ^ i) *
              L x ^ (C * ((i : ℝ) + 1) + CZ * (i : ℝ)) := by
              rw [hLpow_eq]
          _ ≤ ((i.factorial : ℝ) * Bmax bounds i * (48 * Real.exp (2 * R)) ^ i) *
              L x ^ (P0 * ((i : ℝ) + 1)) := by
              have hCoeffNonneg : 0 ≤ (i.factorial : ℝ) * Bmax bounds i *
                  (48 * Real.exp (2 * R)) ^ i := by
                have h0 := hBGnnonneg i
                simpa [hBGn] using h0
              exact mul_le_mul_of_nonneg_left hLpow_le hCoeffNonneg
      -- Combine Loc*Ge = H with 2*P0, then H*Gn = FR with 4*P0 = C1, then to complex.
      have hHCont : ContDiff ℝ (j : ℕ∞) (fun t : Fin 3 → ℝ => localizer t * Ge t) :=
        (hLoc.of_le (by simp)).mul (hGeCont.of_le (by simp))
      have hFRCont : ContDiff ℝ (j : ℕ∞) FR := by
        have hHeq : FR = (fun t : Fin 3 → ℝ => localizer t * Ge t) * Gn := by
          funext t
          simp [hFR, Pi.mul_apply]
        rw [hHeq]
        exact hHCont.mul (hGnCont.of_le (by simp))
      -- First product H = Loc*Ge with P0 -> 2*P0 (explicit sum, no BH name to avoid unfolding).
      have hHAll : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i
          (fun t : Fin 3 → ℝ => localizer t * Ge t) y‖ ≤
          (∑ k ∈ Finset.range (i + 1),
            (i.choose k : ℝ) * localBounds k * BGe (i - k)) *
            L x ^ ((2 * P0) * ((i : ℝ) + 1)) := by
        intro i hi
        have hLocCont_i : ContDiff ℝ (i : ℕ∞) localizer := hLoc.of_le (by simp)
        have hGeCont_i : ContDiff ℝ (i : ℕ∞) Ge :=
          (hGeCont.of_le (by simp) : ContDiff ℝ (i : ℕ∞) Ge)
        have hLocP0_i : ∀ k, k ≤ i → ‖iteratedFDeriv ℝ k localizer y‖ ≤
            localBounds k * L x ^ (P0 * ((k : ℝ) + 1)) := fun k hk => hLocP0 k (le_trans hk hi)
        have hGeP0_i : ∀ k, k ≤ i → ‖iteratedFDeriv ℝ k Ge y‖ ≤
            BGe k * L x ^ (P0 * ((k : ℝ) + 1)) := fun k hk => hGeP0 k (le_trans hk hi)
        exact norm_prod_le_of_bounds (f := localizer) (g := Ge)
          (Bf := localBounds) (Bg := BGe) (P := P0) (Lpow := L x) (y := y) (n := i)
          hLocCont_i hGeCont_i (fun k => (hb k).2) hBGenonneg hP0pos.le hL1 hLpos
          hLocP0_i hGeP0_i
      -- Upgrade Gn from P0 to 2*P0 (same coefficient BGn).
      have hP0le2P0 : P0 ≤ 2 * P0 := by linarith [hP0pos]
      have hGn2P0 : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i Gn y‖ ≤
          BGn i * L x ^ ((2 * P0) * ((i : ℝ) + 1)) := by
        intro i hi
        calc ‖iteratedFDeriv ℝ i Gn y‖ ≤ BGn i * L x ^ (P0 * ((i : ℝ) + 1)) :=
              hGnP0 i hi
          _ ≤ BGn i * L x ^ ((2 * P0) * ((i : ℝ) + 1)) :=
              upgrade_exp_bound hBGnnonneg hL1 hP0le2P0 i
      -- Second product FR = H*Gn with P=2*P0 -> 4*P0 = C1, explicit (no BH name).
      have h2P0nonneg : 0 ≤ 2 * P0 := by linarith [hP0pos]
      have hHCont_j : ContDiff ℝ (j : ℕ∞) (fun t : Fin 3 → ℝ => localizer t * Ge t) :=
        hHCont
      have hGnCont_j : ContDiff ℝ (j : ℕ∞) Gn := hGnCont.of_le (by simp)
      -- Bf for H is explicit inner sum (same as hHAll explicit, no BH name).
      -- Use hHAll explicit directly as hfB with Bf explicit.
      -- Bf for H is explicit inner sum (same as hHAll explicit, no BH name).
      -- Directly prove FR bound (for FR real) as hFRBound2 (no outer duplicate wrapper to avoid unsolved).
      have hBfNonneg : ∀ i, 0 ≤
            (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * localBounds k * BGe (i - k)) := by
          intro i
          apply Finset.sum_nonneg
          intro k _
          apply mul_nonneg
          · apply mul_nonneg
            · exact Nat.cast_nonneg _
            · exact (hb k).2
          · exact hBGenonneg _
      have hHfB : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i
          (fun t : Fin 3 → ℝ => localizer t * Ge t) y‖ ≤
          (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * localBounds k * BGe (i - k)) *
            L x ^ ((2 * P0) * ((i : ℝ) + 1)) :=
        hHAll
      have hGfB : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i Gn y‖ ≤
          BGn i * L x ^ ((2 * P0) * ((i : ℝ) + 1)) := fun i hi => hGn2P0 i hi
      have hHCont2 : ContDiff ℝ (j : ℕ∞) (fun t : Fin 3 → ℝ => localizer t * Ge t) :=
        hHCont
      have hFREq2 : FR =
          (fun t : Fin 3 → ℝ => localizer t * Ge t) * Gn := by
        funext t
        simp [hFR, Pi.mul_apply]
      have hProd2 := norm_prod_le_of_bounds
        (f := fun t : Fin 3 → ℝ => localizer t * Ge t) (g := Gn)
        (Bf := fun i => ∑ k ∈ Finset.range (i + 1),
          (i.choose k : ℝ) * localBounds k * BGe (i - k))
        (Bg := BGn) (P := 2 * P0) (Lpow := L x) (y := y) (n := j)
        hHCont_j hGnCont_j hBfNonneg hBGnnonneg h2P0nonneg hL1 hLpos hHfB hGfB
      -- hProd2 gives double sum with 4*P0 = C1; matches bounds1 inline (no BH) via single unfoldings.
      have hC1eq3 : (2 : ℝ) * (2 * P0) = C1 := by simp [hC1def]; ring
      have hFRBound2 : ‖iteratedFDeriv ℝ j FR y‖ ≤
          bounds1 j * L x ^ (C1 * ((j : ℝ) + 1)) := by
        simpa [hbounds1, hC1eq3] using hProd2
      -- Transfer FR (real) bound to Fclean (complex) via ofRealCLM (norm 1).
      -- This proves the pos-branch goal ‖D^j Fclean‖ ≤ ... (for y in ball).
      have hFcleanEq2 : Fclean = Complex.ofRealCLM ∘ FR := by
        funext t
        simp [hFclean, hFR, Complex.ofRealCLM_apply]
      have hNormL2 : ‖Complex.ofRealCLM‖ = 1 := Complex.ofRealCLM_norm
      have hContAt2 : ContDiffAt ℝ (j : ℕ∞) FR y :=
        (hFRCont.of_le (by simp)).contDiffAt
      calc ‖iteratedFDeriv ℝ j Fclean y‖
          = ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ FR) y‖ := by rw [← hFcleanEq2]
        _ ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j FR y‖ :=
            Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hContAt2 (by simp)
        _ = ‖iteratedFDeriv ℝ j FR y‖ := by rw [hNormL2, one_mul]
        _ ≤ bounds1 j * L x ^ (C1 * ((j : ℝ) + 1)) := hFRBound2
    · -- Outside the ball, the derivative is zero via support.
      have hyTs : y ∉ tsupport Fclean := fun hmem => hyBall (hTsupportSub hmem)
      have hySuppIter : y ∉ Function.support (iteratedFDeriv ℝ j Fclean) :=
        fun hmem => hyTs ((support_iteratedFDeriv_subset j) hmem)
      have hDerivZero : iteratedFDeriv ℝ j Fclean y = 0 := by
        by_contra hNe
        exact hySuppIter (Function.mem_support.mpr hNe)
      rw [hDerivZero]
      simp only [norm_zero]
      apply mul_nonneg _ (Real.rpow_nonneg (le_trans zero_le_one hL1) _)
      exact hbounds1nonneg j
  obtain ⟨a, haInt, haMass, haRepClean, haTail⟩ := hxF Fclean hCleanCont hCleanSupp hCleanBound
  -- Transfer representation from Fclean to pulledCutoff via hFeq and F definition.
  have haRep : ∀ t, pulledCutoff U V Z (U * L x ^ (-K0)) k etae etan localizer t =
      ∫ ξ, a ξ * e (∑ i, ξ i * t i) := by
    intro t
    have hFt : F t = pulledCutoff U V Z (U * L x ^ (-K0)) k etae etan localizer t := by
      simp [hFdef]
    have hFCt : F t = Fclean t := congrFun hFeq t
    rw [← hFt, hFCt]
    exact haRepClean t
  exact ⟨a, haInt, haMass, haRep, haTail⟩

end Erdos821.P6Cut

