import Erdos821.P7Char.SmallConductor

/-! Large conductors: dyadic decomposition of the extracted prime, Fourier separation of
the cutoff, and the large sieve on dyadic conductor blocks. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory Erdos821.Blueprint.Analytic
open scoped Classical

namespace Erdos821.P7Char

open Erdos821.Blueprint

def bandBlock (B0 : Finset ℕ) (k : ℕ) : Finset ℕ := B0.filter (fun p => Nat.log 2 p = k)

/-- Prime-side coefficients on the `k`-th dyadic block. -/
def aco (B0 : Finset ℕ) (h k : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  if n ∈ bandBlock B0 k ∧ Nat.Coprime n h then tw n t else 0

/-- Complementary coefficients. -/
def bco (β : ℕ → ℝ) (h : ℕ) (t : ℝ) (r : ℕ) : ℂ :=
  if Nat.Coprime r h then (β r : ℂ) * tw r t else 0

theorem aco_continuous (B0 : Finset ℕ) (h k n : ℕ) : Continuous (fun t => aco B0 h k t n) := by
  unfold aco
  exact Continuous.if_const _ (tw_continuous n) continuous_const

theorem bco_continuous (β : ℕ → ℝ) (h r : ℕ) : Continuous (fun t => bco β h t r) := by
  unfold bco
  exact Continuous.if_const _ (continuous_const.mul (tw_continuous r)) continuous_const

theorem aco_norm_le (B0 : Finset ℕ) (h k : ℕ) (t : ℝ) (n : ℕ) : ‖aco B0 h k t n‖ ≤ 1 := by
  unfold aco
  split_ifs
  · rw [tw_norm]
  · simp

theorem bco_norm_le (β : ℕ → ℝ) (hβ : ∀ r, 0 ≤ β r) (h : ℕ) (t : ℝ) (r : ℕ) :
    ‖bco β h t r‖ ≤ β r := by
  unfold bco
  split_ifs
  · rw [norm_mul, tw_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ r)]
  · simpa using hβ r

theorem charPoly_continuous {Q : ℕ} (N : ℕ) (a : ℝ → ℕ → ℂ) (ha : ∀ n, Continuous (fun t => a t n))
    (χ : CharacterIndex Q) : Continuous (fun t => charPoly N (a t) χ) := by
  unfold charPoly
  exact continuous_finset_sum _ (fun n _ => (ha n).mul continuous_const)

theorem charPoly_norm_le {Q : ℕ} (N : ℕ) (a : ℕ → ℂ) (χ : CharacterIndex Q) (c : ℕ → ℝ)
    (hc : ∀ n, ‖a n‖ ≤ c n) : ‖charPoly N a χ‖ ≤ ∑ n ∈ Finset.Icc 1 N, c n := by
  unfold charPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [norm_mul]
  exact (mul_le_mul (hc n) (charValue_norm_le χ n) (norm_nonneg _)
    ((norm_nonneg _).trans (hc n))).trans (by rw [mul_one])

theorem bandBlock_subset (B0 : Finset ℕ) (hB0 : ∀ p ∈ B0, 0 < p) (k : ℕ) :
    bandBlock B0 k ⊆ Finset.Icc 1 (2 ^ (k + 1)) := by
  intro p hp
  obtain ⟨hpB, hpk⟩ := Finset.mem_filter.1 hp
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rw [hpk] at hlt
  exact Finset.mem_Icc.2 ⟨hB0 p hpB, hlt.le⟩

/-- Dyadic Fourier representation of the twisted sum. -/
theorem twisted_dyadic (C : CandidateData) (x : ℝ) (hx : 0 < x) (jstar : ℕ)
    (s₀ : C.bands.Slot x)
    (hB : ∀ p ∈ C.bands.slotValues x jstar s₀,
      p.Prime ∧ S56Core.GroupFree (C.bands.groups x) p)
    (hψ : Function.support C.psi ⊆ Set.Icc 1 2) (a : ℝ → ℂ) (hrep : CutoffRep C.psi a)
    (Q h : ℕ) (χ : CharacterIndex Q) :
    twisted (Finset.Icc 1 ⌊2 * x⌋₊) (C.weighted x jstar) h χ =
      ∑ k ∈ (C.bands.slotValues x jstar s₀).image (Nat.log 2),
        ∫ t, a t * (e (-t * Real.log x) *
          (charPoly (2 ^ (k + 1)) (aco (C.bands.slotValues x jstar s₀) h k t) χ *
            charPoly (⌊2 * x⌋₊ / 2 ^ k) (bco (beta C.bands x jstar s₀) h t) χ)) := by
  set B0 := C.bands.slotValues x jstar s₀ with hB0
  set β := beta C.bands x jstar s₀ with hβ
  set M := ⌊2 * x⌋₊ with hM
  have hB0pos : ∀ p ∈ B0, 0 < p := fun p hp => (hB p hp).1.pos
  have hN : ∀ p ∈ B0, M / p ≤ M / 2 ^ (Nat.log 2 p) := by
    intro p hp
    exact Nat.div_le_div_left (Nat.pow_log_le_self 2 (hB0pos p hp).ne') (by positivity)
  rw [twisted_eq_cv, weighted_sum_extract C x hx jstar s₀ hB hψ (cv h χ)
    (fun p => M / 2 ^ (Nat.log 2 p)) hN]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.log 2) (t := B0.image (Nat.log 2))
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hstep : (∑ p ∈ B0.filter (fun p => Nat.log 2 p = k),
      ∑ r ∈ Finset.Icc 1 (M / 2 ^ (Nat.log 2 p)),
        (β r : ℂ) * (C.psi ((p : ℝ) * r / x) : ℂ) * cv h χ (p * r)) =
      ∑ p ∈ bandBlock B0 k, ∑ r ∈ Finset.Icc 1 (M / 2 ^ k),
        cv h χ p * ((β r : ℂ) * cv h χ r) * (C.psi ((p : ℝ) * r / x) : ℂ) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [(Finset.mem_filter.1 hp).2]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [cv_mul]
    ring
  rw [hstep, bilinear_fourier C.psi a hrep x hx (bandBlock B0 k) (Finset.Icc 1 (M / 2 ^ k))
    (fun p hp => hB0pos p (Finset.mem_filter.1 hp).1)
    (fun r hr => (Finset.mem_Icc.1 hr).1) (cv h χ) (fun r => (β r : ℂ) * cv h χ r)]
  congr 1
  ext t
  have hA : (∑ n ∈ bandBlock B0 k, cv h χ n * tw n t) =
      charPoly (2 ^ (k + 1)) (aco B0 h k t) χ := by
    unfold charPoly
    have hterm : ∀ n, aco B0 h k t n * charValue χ n =
        if n ∈ bandBlock B0 k then cv h χ n * tw n t else 0 := by
      intro n
      unfold aco cv
      by_cases hn : n ∈ bandBlock B0 k
      · by_cases hc : Nat.Coprime n h
        · simp [hn, hc]; ring
        · simp [hn, hc]
      · simp [hn]
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_ite_mem,
      Finset.inter_eq_right.2 (bandBlock_subset B0 hB0pos k)]
  have hBsum : (∑ r ∈ Finset.Icc 1 (M / 2 ^ k), ((β r : ℂ) * cv h χ r) * tw r t) =
      charPoly (M / 2 ^ k) (bco β h t) χ := by
    unfold charPoly
    refine Finset.sum_congr rfl (fun r _ => ?_)
    unfold bco cv
    split_ifs <;> ring
  rw [hA, hBsum]

/-- Dyadic conductor blocks cover the large conductors. -/
theorem large_conductor_blocks (Q R : ℕ) (G : CharacterIndex Q → ℝ) (hG : ∀ χ, 0 ≤ G χ) :
    ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => R < fC χ), G χ ≤
      ∑ j ∈ (Finset.range (Nat.log 2 Q + 1)).filter (fun j => R < 2 ^ (j + 1)),
        ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => 2 ^ j ≤ fC χ ∧ fC χ ≤ 2 ^ (j + 1)),
          G χ := by
  have hfQ : ∀ χ : CharacterIndex Q, fC χ ≤ Q := fun χ => by
    have := χ.1.isLt; unfold fC; omega
  have hmaps : ∀ χ ∈ (primitiveCharacters Q).filter (fun χ => R < fC χ),
      Nat.log 2 (fC χ) ∈ (Finset.range (Nat.log 2 Q + 1)).filter (fun j => R < 2 ^ (j + 1)) := by
    intro χ hχ
    have hR := (Finset.mem_filter.1 hχ).2
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le
      (Nat.log_mono_right (hfQ χ))), ?_⟩
    exact lt_trans hR (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro χ hχ
    obtain ⟨hχ1, hj⟩ := Finset.mem_filter.1 hχ
    obtain ⟨hprim, _⟩ := Finset.mem_filter.1 hχ1
    refine Finset.mem_filter.2 ⟨hprim, ?_, ?_⟩
    · rw [← hj]; exact Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
    · rw [← hj]; exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _).le
  · intro χ _ _
    exact hG χ

/-- The uniform dyadic block bound. -/
def blockBB (K : ℝ) (Q R NA NB : ℕ) (βB : ℝ) : ℝ :=
  2 * K * Real.sqrt (((NA : ℝ) + 1) * βB) *
    (Real.sqrt (((NA : ℝ) + 1) * ((NB : ℝ) + 1)) / ((R : ℝ) + 1) +
      Real.sqrt (Real.log (4 * Q)) * (Real.sqrt ((NA : ℝ) + 1) + Real.sqrt ((NB : ℝ) + 1)) +
      2 * Q * Real.log (4 * Q))

theorem block_bound (K : ℝ) (hK : 0 ≤ K) (hLSK : LSBound K) (Q R j NA NB : ℕ) (hQ : 1 ≤ Q)
    (hj : j ≤ Nat.log 2 Q) (hRj : R < 2 ^ (j + 1)) (a b : ℕ → ℂ) (βB : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : sqNorm (Finset.Icc 1 NB) b ≤ βB) :
    ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => 2 ^ j ≤ fC χ ∧ fC χ ≤ 2 ^ (j + 1)),
        ((fC χ).totient : ℝ)⁻¹ * (‖charPoly NA a χ‖ * ‖charPoly NB b χ‖) ≤
      blockBB K Q R NA NB βB := by
  set Rj : ℝ := ((2 ^ (j + 1) : ℕ) : ℝ) with hRjdef
  set Λj : ℝ := Real.log (2 * Rj) with hΛjdef
  set α := sqNorm (Finset.Icc 1 NA) a
  set β := sqNorm (Finset.Icc 1 NB) b
  have hα0 : 0 ≤ α := Finset.sum_nonneg (fun _ _ => by positivity)
  have hβ0 : 0 ≤ β := Finset.sum_nonneg (fun _ _ => by positivity)
  have hαA : α ≤ (NA : ℝ) + 1 := by
    have : α ≤ ∑ n ∈ Finset.Icc 1 NA, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      have := ha n
      have h0 := norm_nonneg (a n)
      nlinarith
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one] at this
    simp at this
    linarith
  have hRjpos : 0 < Rj := by rw [hRjdef]; positivity
  have hRR : (R : ℝ) + 1 ≤ Rj := by
    rw [hRjdef]; exact_mod_cast hRj
  have hRjQ : Rj ≤ 2 * Q := by
    rw [hRjdef]
    have h1 : 2 ^ j ≤ Q :=
      (Nat.pow_le_pow_right (by norm_num) hj).trans (Nat.pow_log_le_self 2 (by omega))
    have : 2 ^ (j + 1) ≤ 2 * Q := by rw [pow_succ]; omega
    exact_mod_cast this
  have hΛ0 : 0 ≤ Λj := Real.log_nonneg (by
    have : (1 : ℝ) ≤ Rj := by rw [hRjdef]; exact_mod_cast Nat.one_le_two_pow
    linarith)
  have hΛle : Λj ≤ Real.log (4 * Q) := Real.log_le_log (by positivity) (by linarith)
  have hstep1 := block_cauchy K hLSK Q j NA NB a b
  have hstep2 := sqrt_ls_product K α β ((NA : ℝ) + 1) ((NB : ℝ) + 1) Rj Λj hK hα0 hβ0
    (by positivity) (by positivity) hRjpos hΛ0
  refine hstep1.trans (hstep2.trans ?_)
  unfold blockBB
  have hsq1 : Real.sqrt (α * β) ≤ Real.sqrt (((NA : ℝ) + 1) * βB) :=
    Real.sqrt_le_sqrt (mul_le_mul hαA hb hβ0 (by positivity))
  have h2 : Real.sqrt (((NA : ℝ) + 1) * ((NB : ℝ) + 1)) / Rj ≤
      Real.sqrt (((NA : ℝ) + 1) * ((NB : ℝ) + 1)) / ((R : ℝ) + 1) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hRR
  have h3 : Real.sqrt Λj * (Real.sqrt ((NA : ℝ) + 1) + Real.sqrt ((NB : ℝ) + 1)) ≤
      Real.sqrt (Real.log (4 * Q)) * (Real.sqrt ((NA : ℝ) + 1) + Real.sqrt ((NB : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hΛle) (by positivity)
  have h4 : Rj * Λj ≤ 2 * Q * Real.log (4 * Q) := mul_le_mul hRjQ hΛle hΛ0 (by positivity)
  apply mul_le_mul (mul_le_mul_of_nonneg_left hsq1 (by positivity))
    (add_le_add (add_le_add h2 h3) h4) (by positivity) (by positivity)

/-- Large-conductor contribution for one `h`. -/
theorem large_part_bound (C : CandidateData) (x : ℝ) (hx : 0 < x) (jstar : ℕ)
    (s₀ : C.bands.Slot x)
    (hB : ∀ p ∈ C.bands.slotValues x jstar s₀,
      p.Prime ∧ S56Core.GroupFree (C.bands.groups x) p)
    (hψ : Function.support C.psi ⊆ Set.Icc 1 2) (a : ℝ → ℂ) (hrep : CutoffRep C.psi a)
    (K : ℝ) (hK : 0 ≤ K) (hLSK : LSBound K) (Q h R : ℕ) (hQ : 1 ≤ Q) (βB : ℕ → ℝ)
    (hβB : ∀ k, ∑ r ∈ Finset.Icc 1 (⌊2 * x⌋₊ / 2 ^ k), (beta C.bands x jstar s₀ r) ^ 2 ≤ βB k) :
    ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => R < fC χ),
        ((fC χ).totient : ℝ)⁻¹ * ‖twisted (Finset.Icc 1 ⌊2 * x⌋₊) (C.weighted x jstar) h χ‖ ≤
      ∑ k ∈ (C.bands.slotValues x jstar s₀).image (Nat.log 2),
        (∫ t, ‖a t‖) * ((((Finset.range (Nat.log 2 Q + 1)).filter
          (fun j => R < 2 ^ (j + 1))).card : ℝ) *
            blockBB K Q R (2 ^ (k + 1)) (⌊2 * x⌋₊ / 2 ^ k) (βB k)) := by
  set B0 := C.bands.slotValues x jstar s₀ with hB0
  set β := beta C.bands x jstar s₀ with hβ
  set M := ⌊2 * x⌋₊ with hM
  set P := (primitiveCharacters Q).filter (fun χ => R < fC χ)
  set J := (Finset.range (Nat.log 2 Q + 1)).filter (fun j => R < 2 ^ (j + 1))
  have hβ0 : ∀ r, 0 ≤ β r := fun r => beta_nonneg C.bands x jstar s₀ r
  set g : ℕ → CharacterIndex Q → ℝ → ℂ := fun k χ t => e (-t * Real.log x) *
    (charPoly (2 ^ (k + 1)) (aco B0 h k t) χ * charPoly (M / 2 ^ k) (bco β h t) χ) with hg
  calc ∑ χ ∈ P, ((fC χ).totient : ℝ)⁻¹ *
        ‖twisted (Finset.Icc 1 M) (C.weighted x jstar) h χ‖
      ≤ ∑ χ ∈ P, ((fC χ).totient : ℝ)⁻¹ * ∑ k ∈ B0.image (Nat.log 2),
          ‖∫ t, a t * g k χ t‖ := by
        apply Finset.sum_le_sum
        intro χ _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [twisted_dyadic C x hx jstar s₀ hB hψ a hrep Q h χ]
        exact norm_sum_le _ _
    _ = ∑ k ∈ B0.image (Nat.log 2), ∑ χ ∈ P, ((fC χ).totient : ℝ)⁻¹ *
          ‖∫ t, a t * g k χ t‖ := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        apply sum_norm_integral_le P a hrep.1 (fun χ => ((fC χ).totient : ℝ)⁻¹)
          (fun _ _ => by positivity) (g k)
          (fun χ _ => (e_continuous_lin _).mul
            ((charPoly_continuous _ _ (fun n => aco_continuous B0 h k n) χ).mul
              (charPoly_continuous _ _ (fun r => bco_continuous β h r) χ)))
          ((2 ^ (k + 1) : ℕ) * ∑ r ∈ Finset.Icc 1 (M / 2 ^ k), β r)
        · intro χ _ t
          rw [hg]
          simp only
          rw [norm_mul, e_norm, one_mul, norm_mul]
          apply mul_le_mul
          · refine (charPoly_norm_le _ _ χ (fun _ => 1) (aco_norm_le B0 h k t)).trans ?_
            simp
          · exact charPoly_norm_le _ _ χ β (bco_norm_le β hβ0 h t)
          · exact norm_nonneg _
          · positivity
        · intro t
          have hnorm : ∀ χ, ‖g k χ t‖ = ‖charPoly (2 ^ (k + 1)) (aco B0 h k t) χ‖ *
              ‖charPoly (M / 2 ^ k) (bco β h t) χ‖ := by
            intro χ
            rw [hg]
            simp only
            rw [norm_mul, e_norm, one_mul, norm_mul]
          simp_rw [hnorm]
          refine (large_conductor_blocks Q R _ (fun χ => by positivity)).trans ?_
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hjr, hjR⟩ := Finset.mem_filter.1 hj
          apply block_bound K hK hLSK Q R j _ _ hQ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hjr))
            hjR _ _ (βB k) (aco_norm_le B0 h k t)
          refine le_trans ?_ (hβB k)
          apply Finset.sum_le_sum
          intro r _
          have := bco_norm_le β hβ0 h t r
          have h0 := norm_nonneg (bco β h t r)
          nlinarith

end Erdos821.P7Char
