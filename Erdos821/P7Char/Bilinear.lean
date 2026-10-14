import Erdos821.P7Char.Orthogonality

/-! The multiplicative large sieve in the character-index form, the Cauchy–Schwarz
dyadic block estimate, and an integral exchange lemma. -/
noncomputable section
open scoped BigOperators
open Filter MeasureTheory Erdos821.Blueprint.Analytic
open scoped Classical

namespace Erdos821.P7Char

open Erdos821.Blueprint

/-- Character polynomial `∑_{n ≤ N} a n χ(n)`. -/
def charPoly {Q : ℕ} (N : ℕ) (a : ℕ → ℂ) (χ : CharacterIndex Q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * charValue χ n

/-- The large sieve inequality over primitive character indices of level at most `R`. -/
def LSBound (K : ℝ) : Prop :=
  ∀ (Q R N : ℕ) (a : ℕ → ℂ),
    ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => fC χ ≤ R),
      ((fC χ : ℝ) / (fC χ).totient) * ‖charPoly N a χ‖ ^ 2 ≤
    K * (N + 1 + (R : ℝ) ^ 2 * Real.log (2 * R)) * sqNorm (Finset.Icc 1 N) a

theorem largeSieve_prim (hLS : MultiplicativeLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ LSBound K := by
  obtain ⟨K, hK, hLS⟩ := hLS
  refine ⟨K, hK, ?_⟩
  intro Q R N a
  set g : ℕ → ℝ := fun m => ((m + 1 : ℕ) : ℝ) / Nat.totient (m + 1) *
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (m + 1))).filter
        DirichletCharacter.IsPrimitive,
      ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod (m + 1))‖ ^ 2 with hg
  have hLHS : (∑ χ ∈ (primitiveCharacters Q).filter (fun χ => fC χ ≤ R),
        ((fC χ : ℝ) / (fC χ).totient) * ‖charPoly N a χ‖ ^ 2) =
      ∑ m ∈ Finset.range (min Q R), g m := by
    rw [primitiveCharacters, Finset.filter_filter, Finset.sum_filter, Fintype.sum_sigma]
    rw [show (∑ m ∈ Finset.range (min Q R), g m) =
        ∑ r : Fin Q, if r.val + 1 ≤ R then g r.val else 0 from ?_]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      by_cases hr : r.val + 1 ≤ R
      · rw [if_pos hr, hg]
        simp only
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        by_cases hc : c.IsPrimitive
        · simp [hc, hr, fC, charPoly, charValue]
        · simp [hc]
      · rw [if_neg hr]
        refine Finset.sum_eq_zero (fun c _ => ?_)
        simp [fC, hr]
    · rw [Fin.sum_univ_eq_sum_range (fun m => if m + 1 ≤ R then g m else 0) Q,
        ← Finset.sum_filter]
      congr 1
      ext m
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
  rw [hLHS, ← Fin.sum_univ_eq_sum_range g (min Q R)]
  refine le_trans (le_of_eq rfl) ((hLS N (min Q R) a).trans ?_)
  have hsq : 0 ≤ sqNorm (Finset.Icc 1 N) a := Finset.sum_nonneg (fun _ _ => by positivity)
  apply mul_le_mul_of_nonneg_right _ hsq
  apply mul_le_mul_of_nonneg_left _ hK.le
  have hRlog : 0 ≤ (R : ℝ) ^ 2 * Real.log (2 * R) := by
    rcases Nat.eq_zero_or_pos R with hR | hR
    · simp [hR]
    · have : (1 : ℝ) ≤ R := by exact_mod_cast hR
      exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hmono : (((min Q R : ℕ) : ℝ)) ^ 2 * Real.log (2 * ((min Q R : ℕ) : ℝ)) ≤
      (R : ℝ) ^ 2 * Real.log (2 * R) := by
    rcases Nat.eq_zero_or_pos (min Q R) with h0 | hpos
    · rw [h0]; simpa using hRlog
    · have hmR : ((min Q R : ℕ) : ℝ) ≤ R := by exact_mod_cast min_le_right Q R
      have h1' : (1 : ℝ) ≤ ((min Q R : ℕ) : ℝ) := by exact_mod_cast hpos
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hmR 2)
        (Real.log_le_log (by positivity) (by linarith)) (Real.log_nonneg (by linarith))
        (by positivity)
  linarith

theorem block_cauchy (K : ℝ) (hLSK : LSBound K) (Q j NA NB : ℕ) (a b : ℕ → ℂ) :
    ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => 2 ^ j ≤ fC χ ∧ fC χ ≤ 2 ^ (j + 1)),
        ((fC χ).totient : ℝ)⁻¹ * (‖charPoly NA a χ‖ * ‖charPoly NB b χ‖) ≤
      (2 / ((2 ^ (j + 1) : ℕ) : ℝ)) *
        (Real.sqrt (K * (NA + 1 + ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
            Real.log (2 * ((2 ^ (j + 1) : ℕ) : ℝ))) * sqNorm (Finset.Icc 1 NA) a) *
          Real.sqrt (K * (NB + 1 + ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
            Real.log (2 * ((2 ^ (j + 1) : ℕ) : ℝ))) * sqNorm (Finset.Icc 1 NB) b)) := by
  set R : ℕ := 2 ^ (j + 1) with hRdef
  have hR : (0 : ℝ) < R := by positivity
  set S := (primitiveCharacters Q).filter (fun χ => 2 ^ j ≤ fC χ ∧ fC χ ≤ 2 ^ (j + 1))
  set T := (primitiveCharacters Q).filter (fun χ => fC χ ≤ R)
  set w : CharacterIndex Q → ℝ := fun χ => (fC χ : ℝ) / (fC χ).totient with hw
  have hw0 : ∀ χ, 0 ≤ w χ := fun χ => by positivity
  have hST : S ⊆ T := by
    intro χ hχ
    obtain ⟨hp, _, h2⟩ := Finset.mem_filter.1 hχ
    exact Finset.mem_filter.2 ⟨hp, h2⟩
  calc
    _ ≤ ∑ χ ∈ S, (2 / (R : ℝ)) * (w χ * (‖charPoly NA a χ‖ * ‖charPoly NB b χ‖)) := by
        apply Finset.sum_le_sum
        intro χ hχ
        obtain ⟨_, h1, _⟩ := Finset.mem_filter.1 hχ
        have hX : 0 ≤ ‖charPoly NA a χ‖ * ‖charPoly NB b χ‖ := by positivity
        have hφ : (0 : ℝ) < (fC χ).totient := by
          exact_mod_cast Nat.totient_pos.2 (Nat.succ_pos _)
        have hf2 : (R : ℝ) ≤ 2 * (fC χ : ℝ) := by
          have : R ≤ 2 * fC χ := by rw [hRdef, pow_succ]; omega
          exact_mod_cast this
        have hle : ((fC χ).totient : ℝ)⁻¹ ≤ (2 / (R : ℝ)) * w χ := by
          rw [hw, show (2 / (R : ℝ)) * ((fC χ : ℝ) / (fC χ).totient) =
            (2 * (fC χ : ℝ) / R) * ((fC χ).totient : ℝ)⁻¹ by ring]
          exact le_mul_of_one_le_left (inv_nonneg.2 hφ.le) (by rw [le_div_iff₀ hR]; linarith)
        calc ((fC χ).totient : ℝ)⁻¹ * (‖charPoly NA a χ‖ * ‖charPoly NB b χ‖)
            ≤ ((2 / (R : ℝ)) * w χ) * (‖charPoly NA a χ‖ * ‖charPoly NB b χ‖) :=
              mul_le_mul_of_nonneg_right hle hX
          _ = _ := by ring
    _ ≤ ∑ χ ∈ T, (2 / (R : ℝ)) * (w χ * (‖charPoly NA a χ‖ * ‖charPoly NB b χ‖)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hST
        intro χ _ _
        have := hw0 χ
        positivity
    _ = (2 / (R : ℝ)) * ∑ χ ∈ T, (Real.sqrt (w χ) * ‖charPoly NA a χ‖) *
          (Real.sqrt (w χ) * ‖charPoly NB b χ‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [mul_mul_mul_comm, Real.mul_self_sqrt (hw0 χ)]
    _ ≤ (2 / (R : ℝ)) * (Real.sqrt (∑ χ ∈ T, (Real.sqrt (w χ) * ‖charPoly NA a χ‖) ^ 2) *
          Real.sqrt (∑ χ ∈ T, (Real.sqrt (w χ) * ‖charPoly NB b χ‖) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by positivity)
    _ = (2 / (R : ℝ)) * (Real.sqrt (∑ χ ∈ T, w χ * ‖charPoly NA a χ‖ ^ 2) *
          Real.sqrt (∑ χ ∈ T, w χ * ‖charPoly NB b χ‖ ^ 2)) := by
        simp_rw [mul_pow, Real.sq_sqrt (hw0 _)]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (Real.sqrt_le_sqrt (hLSK Q R NA a)) (Real.sqrt_le_sqrt (hLSK Q R NB b))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem sqrt_ls_product (K α β A B R Λ : ℝ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 < R) (hΛ : 0 ≤ Λ) :
    (2 / R) * (Real.sqrt (K * (A + R ^ 2 * Λ) * α) * Real.sqrt (K * (B + R ^ 2 * Λ) * β)) ≤
      2 * K * Real.sqrt (α * β) *
        (Real.sqrt (A * B) / R + Real.sqrt Λ * (Real.sqrt A + Real.sqrt B) + R * Λ) := by
  have hs := Real.sqrt_nonneg A
  have ht := Real.sqrt_nonneg B
  have hl := Real.sqrt_nonneg Λ
  have hA2 := Real.sq_sqrt hA
  have hB2 := Real.sq_sqrt hB
  have hl2 := Real.sq_sqrt hΛ
  set s := Real.sqrt A
  set t := Real.sqrt B
  set l := Real.sqrt Λ
  have key : (A + R ^ 2 * Λ) * (B + R ^ 2 * Λ) ≤ (s * t + R * l * (s + t) + R ^ 2 * Λ) ^ 2 := by
    rw [← hA2, ← hB2, ← hl2]
    have hR0 := hR.le
    have e : (s * t + R * l * (s + t) + R ^ 2 * l ^ 2) ^ 2 -
        (s ^ 2 + R ^ 2 * l ^ 2) * (t ^ 2 + R ^ 2 * l ^ 2) =
        4 * R ^ 2 * l ^ 2 * s * t + 2 * s * t * R * l * (s + t) + 2 * R ^ 3 * l ^ 3 * (s + t) := by
      ring
    have : 0 ≤ 4 * R ^ 2 * l ^ 2 * s * t + 2 * s * t * R * l * (s + t) +
        2 * R ^ 3 * l ^ 3 * (s + t) := by positivity
    linarith
  have hsq : Real.sqrt ((A + R ^ 2 * Λ) * (B + R ^ 2 * Λ)) ≤
      s * t + R * l * (s + t) + R ^ 2 * Λ := by
    calc _ ≤ Real.sqrt ((s * t + R * l * (s + t) + R ^ 2 * Λ) ^ 2) := Real.sqrt_le_sqrt key
      _ = _ := Real.sqrt_sq (by positivity)
  have hprod : Real.sqrt (K * (A + R ^ 2 * Λ) * α) * Real.sqrt (K * (B + R ^ 2 * Λ) * β) =
      K * Real.sqrt (α * β) * Real.sqrt ((A + R ^ 2 * Λ) * (B + R ^ 2 * Λ)) := by
    rw [← Real.sqrt_mul (by positivity),
      show K * (A + R ^ 2 * Λ) * α * (K * (B + R ^ 2 * Λ) * β) =
        K ^ 2 * (α * β) * ((A + R ^ 2 * Λ) * (B + R ^ 2 * Λ)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hK]
  have hst : Real.sqrt (A * B) = s * t := Real.sqrt_mul hA B
  rw [hprod, hst]
  have hKab : 0 ≤ K * Real.sqrt (α * β) := by positivity
  calc 2 / R * (K * Real.sqrt (α * β) * Real.sqrt ((A + R ^ 2 * Λ) * (B + R ^ 2 * Λ)))
      ≤ 2 / R * (K * Real.sqrt (α * β) * (s * t + R * l * (s + t) + R ^ 2 * Λ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsq hKab
    _ = _ := by
        field_simp

/-! ### Integral exchange -/

theorem sum_norm_integral_le {ι : Type*} (s : Finset ι) (a : ℝ → ℂ) (ha : Integrable a)
    (wt : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ wt i) (g : ι → ℝ → ℂ) (hgc : ∀ i ∈ s, Continuous (g i))
    (M : ℝ) (hgM : ∀ i ∈ s, ∀ t, ‖g i t‖ ≤ M) (B : ℝ)
    (hB : ∀ t, ∑ i ∈ s, wt i * ‖g i t‖ ≤ B) :
    ∑ i ∈ s, wt i * ‖∫ t, a t * g i t‖ ≤ (∫ t, ‖a t‖) * B := by
  have hint : ∀ i ∈ s, Integrable (fun t => ‖a t‖ * ‖g i t‖) := by
    intro i hi
    refine ha.norm.mul_bdd (c := M) (hgc i hi).norm.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_norm]
    exact hgM i hi t
  calc ∑ i ∈ s, wt i * ‖∫ t, a t * g i t‖
      ≤ ∑ i ∈ s, wt i * ∫ t, ‖a t‖ * ‖g i t‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (hw i hi)
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        congr 1
        ext t
        rw [norm_mul]
    _ = ∫ t, ∑ i ∈ s, wt i * (‖a t‖ * ‖g i t‖) := by
        rw [integral_finset_sum]
        · refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [integral_const_mul]
        · intro i hi
          exact (hint i hi).const_mul _
    _ ≤ ∫ t, ‖a t‖ * B := by
        apply integral_mono
        · exact integrable_finset_sum _ (fun i hi => (hint i hi).const_mul _)
        · exact ha.norm.mul_const B
        · intro t
          simp only
          calc ∑ i ∈ s, wt i * (‖a t‖ * ‖g i t‖) = ‖a t‖ * ∑ i ∈ s, wt i * ‖g i t‖ := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                ring
            _ ≤ ‖a t‖ * B := mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)
    _ = (∫ t, ‖a t‖) * B := integral_mul_const B _

end Erdos821.P7Char
