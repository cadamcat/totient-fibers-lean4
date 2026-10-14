import Erdos821.P7Char.Bilinear
import Erdos821.S56.CutoffFourier

/-! Fourier (Mellin) separation of the smooth cutoff `ψ(n r / x)`. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory Erdos821.Blueprint.Analytic
open scoped Classical

namespace Erdos821.P7Char

open Erdos821.Blueprint

/-- Unimodular twist `n^{2π i t}`. -/
def tw (n : ℕ) (t : ℝ) : ℂ := Analytic.mellin n (2 * Real.pi * t)

theorem tw_continuous (n : ℕ) : Continuous (tw n) := by
  unfold tw Analytic.mellin
  apply Complex.continuous_exp.comp
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_const.mul continuous_id))).mul continuous_const

theorem tw_norm (n : ℕ) (t : ℝ) : ‖tw n t‖ = 1 := by
  unfold tw Analytic.mellin
  rw [show Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ) =
      ((2 * Real.pi * t * Real.log n : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem tw_mul (n r : ℕ) (hn : 0 < n) (hr : 0 < r) (t : ℝ) :
    tw (n * r) t = tw n t * tw r t := by
  unfold tw Analytic.mellin
  rw [← Complex.exp_add]
  congr 1
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

theorem e_continuous_lin (c : ℝ) : Continuous (fun t : ℝ => e (-t * c)) := by
  unfold e
  apply Complex.continuous_exp.comp
  exact ((continuous_const.mul (Complex.continuous_ofReal.comp
    ((continuous_neg.comp continuous_id).mul continuous_const))).mul continuous_const)

theorem e_norm (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [show (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) * Complex.I =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem integrable_mul_bdd' (a : ℝ → ℂ) (ha : Integrable a) (g : ℝ → ℂ) (hg : Continuous g)
    (M : ℝ) (hM : ∀ t, ‖g t‖ ≤ M) : Integrable (fun t => a t * g t) :=
  ha.mul_bdd hg.aestronglyMeasurable (ae_of_all _ hM)

/-- Fourier representation of the cutoff (as given by `S56Core.cutoff_fourier`). -/
def CutoffRep (φ : ℝ → ℝ) (a : ℝ → ℂ) : Prop :=
  Integrable a ∧ ∀ u x : ℝ, 0 < u → 0 < x →
    (φ (u / x) : ℂ) = ∫ t, a t * e (-t * Real.log x) * Analytic.mellin u (2 * Real.pi * t)

theorem cutoffRep_of (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hsupp : Function.support φ ⊆ Set.Icc 1 2) :
    ∃ a : ℝ → ℂ, CutoffRep φ a ∧ ∀ n : ℕ, Integrable (fun t => ‖t‖ ^ n * ‖a t‖) := by
  obtain ⟨a, ha, hm, hrep⟩ := S56Core.cutoff_fourier φ hφ hsupp
  exact ⟨a, ⟨ha, hrep⟩, hm⟩

/-- Bilinear separation: the cutoff on `n r` splits into a product of twisted sums. -/
theorem bilinear_fourier (φ : ℝ → ℝ) (a : ℝ → ℂ) (hrep : CutoffRep φ a) (x : ℝ) (hx : 0 < x)
    (S T : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (hT : ∀ r ∈ T, 0 < r) (α γ : ℕ → ℂ) :
    ∑ n ∈ S, ∑ r ∈ T, α n * γ r * (φ ((n : ℝ) * r / x) : ℂ) =
      ∫ t, a t * (e (-t * Real.log x) *
        ((∑ n ∈ S, α n * tw n t) * (∑ r ∈ T, γ r * tw r t))) := by
  obtain ⟨ha, hrep⟩ := hrep
  have hint : ∀ n r : ℕ, ∀ c : ℂ, Integrable (fun t => a t *
      (c * (e (-t * Real.log x) * (tw n t * tw r t)))) := by
    intro n r c
    refine integrable_mul_bdd' a ha _ ?_ ‖c‖ ?_
    · exact continuous_const.mul ((e_continuous_lin _).mul
        ((tw_continuous n).mul (tw_continuous r)))
    · intro t
      rw [norm_mul, norm_mul, norm_mul, e_norm, tw_norm, tw_norm]
      simp
  have hterm : ∀ n ∈ S, ∀ r ∈ T, α n * γ r * (φ ((n : ℝ) * r / x) : ℂ) =
      ∫ t, a t * ((α n * γ r) * (e (-t * Real.log x) * (tw n t * tw r t))) := by
    intro n hn r hr
    have hu : (0 : ℝ) < (n : ℝ) * r := by
      have := hS n hn; have := hT r hr; positivity
    rw [hrep _ x hu hx, ← integral_const_mul]
    congr 1
    ext t
    have hmul : Analytic.mellin ((n : ℝ) * r) (2 * Real.pi * t) = tw n t * tw r t := by
      rw [← tw_mul n r (hS n hn) (hT r hr) t]
      simp [tw]
    rw [hmul]
    ring
  calc
    _ = ∑ n ∈ S, ∑ r ∈ T,
          ∫ t, a t * ((α n * γ r) * (e (-t * Real.log x) * (tw n t * tw r t))) :=
        Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun r hr => hterm n hn r hr))
    _ = ∫ t, ∑ n ∈ S, ∑ r ∈ T,
          a t * ((α n * γ r) * (e (-t * Real.log x) * (tw n t * tw r t))) := by
        rw [integral_finset_sum]
        · refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [integral_finset_sum]
          intro r _
          exact hint n r _
        · intro n _
          exact integrable_finset_sum _ (fun r _ => hint n r _)
    _ = _ := by
        congr 1
        ext t
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring

/-- Harmonic separation for a fixed complementary variable `r`. -/
theorem harmonic_fourier (ψ : ℝ → ℝ) (a₂ : ℝ → ℂ)
    (hrep : CutoffRep (fun y => y * ψ y) a₂) (x : ℝ) (hx : 0 < x) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (r : ℕ) (hr : 0 < r) (α : ℕ → ℂ) :
    ∑ p ∈ S, α p * (ψ ((p : ℝ) * r / x) : ℂ) =
      ((x / r : ℝ) : ℂ) * ∫ t, a₂ t * ((e (-t * Real.log x) * tw r t) *
        ∑ p ∈ S, α p * tw p t / (p : ℂ)) := by
  obtain ⟨ha, hrep⟩ := hrep
  have hint : ∀ p : ℕ, ∀ c : ℂ, Integrable (fun t => a₂ t *
      (c * ((e (-t * Real.log x) * tw r t) * tw p t))) := by
    intro p c
    refine integrable_mul_bdd' a₂ ha _ ?_ ‖c‖ ?_
    · exact continuous_const.mul (((e_continuous_lin _).mul (tw_continuous r)).mul
        (tw_continuous p))
    · intro t
      rw [norm_mul, norm_mul, norm_mul, e_norm, tw_norm, tw_norm]
      simp
  have hterm : ∀ p ∈ S, α p * (ψ ((p : ℝ) * r / x) : ℂ) =
      ((x / r : ℝ) : ℂ) * ∫ t, a₂ t * ((α p / (p : ℂ)) *
        ((e (-t * Real.log x) * tw r t) * tw p t)) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hS p hp
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hu : (0 : ℝ) < (p : ℝ) * r := by positivity
    have hψ : (ψ ((p : ℝ) * r / x) : ℂ) =
        ((x / ((p : ℝ) * r) : ℝ) : ℂ) * (((p : ℝ) * r / x * ψ ((p : ℝ) * r / x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    rw [hψ, hrep _ x hu hx, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    congr 1
    ext t
    have hmul : Analytic.mellin ((p : ℝ) * r) (2 * Real.pi * t) = tw p t * tw r t := by
      rw [← tw_mul p r (hS p hp) hr t]
      simp [tw]
    rw [hmul]
    have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (hS p hp).ne'
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
    try ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← integral_finset_sum]
  · congr 1
    congr 1
    ext t
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  · intro p _
    exact hint p _

/-- An integral against a Fourier coefficient, with an integrand small on `|t| ≤ T0`. -/
theorem integral_split_bound (a : ℝ → ℂ) (ha : Integrable a) (g : ℝ → ℂ) (hg : Continuous g)
    (T0 ε M : ℝ) (hε : 0 ≤ ε) (hM : ∀ t, ‖g t‖ ≤ M) (hsmall : ∀ t, ‖t‖ ≤ T0 → ‖g t‖ ≤ ε) :
    ‖∫ t, a t * g t‖ ≤ ε * (∫ t, ‖a t‖) + M * ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a t‖ := by
  set Sset : Set ℝ := {t : ℝ | T0 < ‖t‖}
  have hSm : MeasurableSet Sset := measurableSet_lt measurable_const continuous_norm.measurable
  have hM0 : ∀ t, 0 ≤ M := fun t => (norm_nonneg _).trans (hM t)
  have hpt : ∀ t, ‖a t * g t‖ ≤ ε * ‖a t‖ + M * Sset.indicator (fun t => ‖a t‖) t := by
    intro t
    rw [norm_mul]
    by_cases ht : t ∈ Sset
    · rw [Set.indicator_of_mem ht]
      have := hM t
      have := norm_nonneg (a t)
      nlinarith
    · rw [Set.indicator_of_notMem ht]
      have ht' : ‖t‖ ≤ T0 := le_of_not_gt ht
      have := hsmall t ht'
      have := norm_nonneg (a t)
      nlinarith
  have hint1 : Integrable (fun t => ε * ‖a t‖) := ha.norm.const_mul ε
  have hint2 : Integrable (fun t => M * Sset.indicator (fun t => ‖a t‖) t) :=
    (ha.norm.indicator hSm).const_mul M
  calc ‖∫ t, a t * g t‖ ≤ ∫ t, ‖a t * g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, (ε * ‖a t‖ + M * Sset.indicator (fun t => ‖a t‖) t) := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun t => norm_nonneg _)
        · exact hint1.add hint2
        · exact ae_of_all _ hpt
    _ = ε * (∫ t, ‖a t‖) + M * ∫ t in Sset, ‖a t‖ := by
        rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
          integral_indicator hSm]

end Erdos821.P7Char
