import Mathlib
import Erdos821.Blueprint.Extraction

open Filter
open Erdos821.Blueprint.Analytic

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Erdos821.Count

/-- For `y > 0`, `log y ≤ 2 * sqrt y`. From `log t ≤ t - 1` with `t = sqrt y`. -/
lemma log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have htpos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (le_of_lt hy)
  have hlog : Real.log y = 2 * Real.log (Real.sqrt y) := by
    conv_lhs => rw [← hsq]
    rw [Real.log_pow]
    norm_cast
  rw [hlog]
  have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos htpos
  linarith [Real.sqrt_nonneg y]

/-- `L x = log x` tends to infinity. -/
lemma tendsto_L : Tendsto (Erdos821.Blueprint.Analytic.L) atTop atTop := by
  unfold Erdos821.Blueprint.Analytic.L
  exact Real.tendsto_log_atTop

/-- Eventually `L x` exceeds any constant. -/
lemma eventually_L_ge (C : ℝ) : ∀ᶠ x : ℝ in atTop, C ≤ Erdos821.Blueprint.Analytic.L x :=
  tendsto_L.eventually_ge_atTop C

/-- Eventually `sqrt (L x)` exceeds any nonnegative constant. -/
lemma eventually_sqrt_ge {M : ℝ} (hM : 0 ≤ M) :
    ∀ᶠ x : ℝ in atTop, M ≤ Real.sqrt (Erdos821.Blueprint.Analytic.L x) := by
  have h : ∀ᶠ x : ℝ in atTop, M ^ 2 ≤ Erdos821.Blueprint.Analytic.L x :=
    eventually_L_ge (M ^ 2)
  filter_upwards [h] with x hx
  have hLnn : 0 ≤ Erdos821.Blueprint.Analytic.L x :=
    le_trans (sq_nonneg M) hx
  rw [Real.le_sqrt hM hLnn]
  exact hx

/-- Absorption of `L`-powers and `exp (K sqrt L)` into `x ^ σ`:
for fixed `K > 0`, `e`, `σ > 0`, `c > 0`, eventually
`L x ^ e * exp (K sqrt (L x)) * c⁻¹ ≤ x ^ σ`. -/
lemma absorb (K e σ c : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      Erdos821.Blueprint.Analytic.L x ^ e *
        Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) *
        c⁻¹ ≤ x ^ σ := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  -- Thresholds for `sqrt (L x)` and `L x`.
  set S : ℝ := max (3 * K / σ) (max (6 * e / σ) 0) with hSdef
  have hS1 : 3 * K / σ ≤ S := le_max_left _ _
  have hS2 : 6 * e / σ ≤ S :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hSnn : 0 ≤ S := by
    have h1 : 0 < 3 * K / σ := by positivity
    exact le_trans (le_of_lt h1) hS1
  -- `L x` must exceed `S ^ 2` (for the sqrt bounds), `1` (for sign control),
  -- and `3 log (c⁻¹) / σ` (for the constant).
  set C₀ : ℝ := max 1 (max (S ^ 2) (3 * Real.log (c⁻¹) / σ)) with hC₀def
  have hC1 : 1 ≤ C₀ := le_max_left _ _
  have hCS : S ^ 2 ≤ C₀ :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCc : 3 * Real.log (c⁻¹) / σ ≤ C₀ :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  filter_upwards [eventually_L_ge C₀, eventually_ge_atTop (Real.exp 1)]
    with x hxL hxx
  have hexp1pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hxpos : 0 < x := lt_of_lt_of_le hexp1pos hxx
  have hLpos : 0 < Erdos821.Blueprint.Analytic.L x := by
    linarith [hxL, hC1]
  have hLnn : 0 ≤ Erdos821.Blueprint.Analytic.L x := le_of_lt hLpos
  have hLge1 : 1 ≤ Erdos821.Blueprint.Analytic.L x := le_trans hC1 hxL
  have hlogLnn : 0 ≤ Real.log (Erdos821.Blueprint.Analytic.L x) :=
    Real.log_nonneg hLge1
  have hsqrt_nn : 0 ≤ Real.sqrt (Erdos821.Blueprint.Analytic.L x) :=
    Real.sqrt_nonneg _
  -- `sqrt (L x) ≥ S`.
  have hsqrtS : S ≤ Real.sqrt (Erdos821.Blueprint.Analytic.L x) := by
    have hSq : S ^ 2 ≤ Erdos821.Blueprint.Analytic.L x := le_trans hCS hxL
    rw [Real.le_sqrt hSnn hLnn]
    exact hSq
  have hLsq : Erdos821.Blueprint.Analytic.L x =
      Real.sqrt (Erdos821.Blueprint.Analytic.L x) ^ 2 :=
    (Real.sq_sqrt hLnn).symm
  -- Three log-domain bounds, each `≤ (σ / 3) * L x`.
  have hB1 : K * Real.sqrt (Erdos821.Blueprint.Analytic.L x) ≤
      σ / 3 * Erdos821.Blueprint.Analytic.L x := by
    have hKle : K ≤ σ / 3 * Real.sqrt (Erdos821.Blueprint.Analytic.L x) := by
      have h1 : 3 * K / σ ≤ Real.sqrt (Erdos821.Blueprint.Analytic.L x) :=
        le_trans hS1 hsqrtS
      have hσ3 : 0 < σ / 3 := by linarith
      have heq : σ / 3 * (3 * K / σ) = K := by
        apply mul_right_cancel₀ hσne
        calc (σ / 3 * (3 * K / σ)) * σ
            = σ / 3 * ((3 * K / σ) * σ) := by ring
          _ = σ / 3 * (3 * K) := by rw [div_mul_cancel₀ (3 * K) hσne]
          _ = σ * K := by ring
          _ = K * σ := by ring
      calc K = σ / 3 * (3 * K / σ) := heq.symm
        _ ≤ σ / 3 * Real.sqrt (Erdos821.Blueprint.Analytic.L x) := by
            apply mul_le_mul_of_nonneg_left h1 (le_of_lt hσ3)
    calc K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)
        ≤ (σ / 3 * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) *
          Real.sqrt (Erdos821.Blueprint.Analytic.L x) :=
          mul_le_mul_of_nonneg_right hKle hsqrt_nn
      _ = σ / 3 * (Real.sqrt (Erdos821.Blueprint.Analytic.L x) ^ 2) := by ring
      _ = σ / 3 * Erdos821.Blueprint.Analytic.L x := by rw [Real.sq_sqrt hLnn]
  have hB2 : e * Real.log (Erdos821.Blueprint.Analytic.L x) ≤
      σ / 3 * Erdos821.Blueprint.Analytic.L x := by
    by_cases he : e ≤ 0
    · have h1 : e * Real.log (Erdos821.Blueprint.Analytic.L x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg he hlogLnn
      have h2 : 0 ≤ σ / 3 * Erdos821.Blueprint.Analytic.L x := by
        apply mul_nonneg _ hLnn
        linarith
      linarith
    · have hepos : 0 < e := lt_of_not_ge he
      have hlogle : Real.log (Erdos821.Blueprint.Analytic.L x) ≤
          2 * Real.sqrt (Erdos821.Blueprint.Analytic.L x) :=
        log_le_two_sqrt hLpos
      have h1 : e * Real.log (Erdos821.Blueprint.Analytic.L x) ≤
          e * (2 * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) :=
        mul_le_mul_of_nonneg_left hlogle (le_of_lt hepos)
      have h2 : e * (2 * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) ≤
          σ / 3 * Erdos821.Blueprint.Analytic.L x := by
        have heS : 6 * e / σ ≤ Real.sqrt (Erdos821.Blueprint.Analytic.L x) :=
          le_trans hS2 hsqrtS
        have hσ3 : 0 < σ / 3 := by linarith
        have he_le : 2 * e ≤ σ / 3 * Real.sqrt (Erdos821.Blueprint.Analytic.L x) := by
          have heq : 6 * e / σ * (σ / 3) = 2 * e := by
            calc 6 * e / σ * (σ / 3) = (6 * e / σ * σ) / 3 := by rw [← mul_div_assoc]
              _ = (6 * e) / 3 := by rw [div_mul_cancel₀ (6 * e) hσne]
              _ = 2 * e := by ring
          calc 2 * e = 6 * e / σ * (σ / 3) := heq.symm
            _ ≤ Real.sqrt (Erdos821.Blueprint.Analytic.L x) * (σ / 3) :=
                mul_le_mul_of_nonneg_right heS (le_of_lt hσ3)
            _ = σ / 3 * Real.sqrt (Erdos821.Blueprint.Analytic.L x) := by ring
        calc e * (2 * Real.sqrt (Erdos821.Blueprint.Analytic.L x))
            = (2 * e) * Real.sqrt (Erdos821.Blueprint.Analytic.L x) := by ring
          _ ≤ (σ / 3 * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) *
              Real.sqrt (Erdos821.Blueprint.Analytic.L x) :=
              mul_le_mul_of_nonneg_right he_le hsqrt_nn
          _ = σ / 3 * (Real.sqrt (Erdos821.Blueprint.Analytic.L x) ^ 2) := by ring
          _ = σ / 3 * Erdos821.Blueprint.Analytic.L x := by rw [Real.sq_sqrt hLnn]
      linarith
  have hB3 : Real.log (c⁻¹) ≤ σ / 3 * Erdos821.Blueprint.Analytic.L x := by
    by_cases hc1 : c ≥ 1
    · have hlogle : Real.log (c⁻¹) ≤ 0 := by
        rw [Real.log_inv]
        have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
        linarith
      have h2 : 0 ≤ σ / 3 * Erdos821.Blueprint.Analytic.L x := by
        apply mul_nonneg _ hLnn
        linarith
      linarith
    · have hclt : c < 1 := lt_of_not_ge hc1
      have h1 : 3 * Real.log (c⁻¹) / σ ≤ Erdos821.Blueprint.Analytic.L x :=
        le_trans hCc hxL
      have hσ3 : 0 < σ / 3 := by linarith
      have heq : σ / 3 * (3 * Real.log (c⁻¹) / σ) = Real.log (c⁻¹) := by
        apply mul_right_cancel₀ hσne
        calc (σ / 3 * (3 * Real.log (c⁻¹) / σ)) * σ
            = σ / 3 * ((3 * Real.log (c⁻¹) / σ) * σ) := by ring
          _ = σ / 3 * (3 * Real.log (c⁻¹)) := by rw [div_mul_cancel₀ (3 * Real.log (c⁻¹)) hσne]
          _ = Real.log (c⁻¹) * σ := by ring
      calc Real.log (c⁻¹) = σ / 3 * (3 * Real.log (c⁻¹) / σ) := heq.symm
        _ ≤ σ / 3 * Erdos821.Blueprint.Analytic.L x :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hσ3)
  have hlog_sum : e * Real.log (Erdos821.Blueprint.Analytic.L x) +
      K * Real.sqrt (Erdos821.Blueprint.Analytic.L x) + Real.log (c⁻¹) ≤
      σ * Erdos821.Blueprint.Analytic.L x := by
    have hσ3 : σ / 3 * Erdos821.Blueprint.Analytic.L x * 3 =
        σ * Erdos821.Blueprint.Analytic.L x := by ring
    linarith [hB1, hB2, hB3]
  -- Exponentiate.
  have hLrpow : Erdos821.Blueprint.Analytic.L x ^ e =
      Real.exp (Real.log (Erdos821.Blueprint.Analytic.L x) * e) :=
    Real.rpow_def_of_pos hLpos e
  have hxrpow : x ^ σ = Real.exp (Real.log x * σ) :=
    Real.rpow_def_of_pos hxpos σ
  have hLdef : Erdos821.Blueprint.Analytic.L x = Real.log x := rfl
  have hcInv : c⁻¹ = Real.exp (Real.log (c⁻¹)) :=
    (Real.exp_log (inv_pos.mpr hc)).symm
  calc Erdos821.Blueprint.Analytic.L x ^ e *
        Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) * c⁻¹
      = Real.exp (Real.log (Erdos821.Blueprint.Analytic.L x) * e +
          K * Real.sqrt (Erdos821.Blueprint.Analytic.L x) + Real.log (c⁻¹)) := by
        conv_lhs => rw [hLrpow, hcInv, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (Real.log x * σ) := by
        apply Real.exp_le_exp.mpr
        rw [← hLdef]
        linarith [hlog_sum]
    _ = x ^ σ := hxrpow.symm

/-- Eventually `2 ≤ x ^ δ` for `δ > 0`, via `L x ≥ log 2 / δ`. -/
lemma eventually_two_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ x ^ δ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := Real.log 2 / δ with hCdef
  filter_upwards [eventually_L_ge C, eventually_ge_atTop (Real.exp 1)]
    with x hxL hxx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxx
  have hxrpow : x ^ δ = Real.exp (Real.log x * δ) :=
    Real.rpow_def_of_pos hxpos δ
  have hLdef : Erdos821.Blueprint.Analytic.L x = Real.log x := rfl
  have h2 : (2 : ℝ) = Real.exp (Real.log 2) :=
    (Real.exp_log (by norm_num)).symm
  rw [h2, hxrpow]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log 2 ≤ Erdos821.Blueprint.Analytic.L x * δ := by
    have hC_le : C ≤ Erdos821.Blueprint.Analytic.L x := hxL
    rw [hCdef] at hC_le
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have : Real.log 2 / δ * δ = Real.log 2 := div_mul_cancel₀ _ hδne
    calc Real.log 2 = Real.log 2 / δ * δ := this.symm
      _ ≤ Erdos821.Blueprint.Analytic.L x * δ :=
          mul_le_mul_of_nonneg_right hC_le (le_of_lt hδ)
  rw [← hLdef]
  linarith [h1]

/-- Injection image: `2 * u + 1` lies in the smooth shifted primes when `u`
is supported, prime-generating, and `u`-smooth, given `2 ≤ x ^ δ`. -/
lemma mem_smooth_of_support {δ x : ℝ} (hx5 : 5 ≤ x)
    (h2le : (2 : ℝ) ≤ x ^ δ)
    {u : ℕ} (hxu : x ≤ (u : ℝ)) (hxu2 : (u : ℝ) ≤ 2 * x)
    (hprime : Nat.Prime (2 * u + 1))
    (hsmooth_u : ∀ q : ℕ, q.Prime → q ∣ u → (q : ℝ) ≤ x ^ δ) :
    (2 * u + 1) ∈ Erdos821.smoothShiftedPrimes δ x := by
  unfold Erdos821.smoothShiftedPrimes
  rw [Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨?_, ?_⟩, hprime, ?_⟩
  · -- `⌊2 * x⌋₊ < 2 * u + 1`
    have hfl : ((⌊2 * x⌋₊ : ℕ) : ℝ) ≤ 2 * x :=
      Nat.floor_le (by positivity)
    have hlt : ((⌊2 * x⌋₊ : ℕ) : ℝ) < ((2 * u + 1 : ℕ) : ℝ) := by
      have h1 : (2 : ℝ) * x ≤ 2 * (u : ℝ) := by linarith [hxu]
      have h2 : 2 * (u : ℝ) < 2 * (u : ℝ) + 1 := by linarith
      have h3 : ((2 * u + 1 : ℕ) : ℝ) = 2 * (u : ℝ) + 1 := by push_cast; ring
      linarith [hfl, h1, h2, h3]
    exact_mod_cast hlt
  · -- `2 * u + 1 ≤ ⌊5 * x⌋₊`
    have hle : ((2 * u + 1 : ℕ) : ℝ) ≤ 5 * x := by
      have h3 : ((2 * u + 1 : ℕ) : ℝ) = 2 * (u : ℝ) + 1 := by push_cast; ring
      have hx1 : (1 : ℝ) ≤ x := by linarith
      linarith [hxu2, hx1, h3]
    exact Nat.le_floor hle
  · -- smoothness of `(2 * u + 1) - 1 = 2 * u`
    intro q hq hqdvd
    have hsub : (2 * u + 1) - 1 = 2 * u := Nat.add_sub_cancel _ _
    rw [hsub] at hqdvd
    have hqdvd2 : q ∣ 2 * u := hqdvd
    rw [hq.dvd_mul] at hqdvd2
    cases hqdvd2 with
    | inl h2 =>
      have hq2 : q = 2 := by
        have h := (Nat.dvd_prime Nat.prime_two).mp h2
        cases h with
        | inl h1 => exact absurd h1 (hq.ne_one)
        | inr h2 => exact h2
      rw [hq2]
      exact h2le
    | inr hu => exact hsmooth_u q hq hu

/-- Pointwise prime-mass upper bound via the smooth count. -/
lemma primeMass_le_card_mul {δ x : ℝ} {C : Erdos821.Blueprint.CandidateData}
    {jstar : ℕ} {K : ℝ}
    (hx5 : 5 ≤ x) (h2le : (2 : ℝ) ≤ x ^ δ)
    (hup : ∀ u : ℕ, C.weighted x jstar u ≤
      Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)))
    (hsupp : ∀ u : ℕ, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x ∧
        ∀ p : ℕ, p.Prime → p ∣ u → (p : ℝ) ≤ x ^ δ) :
    C.primeMass x jstar ≤
      ((Erdos821.smoothShiftedPrimes δ x).card : ℝ) *
        Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) := by
  open Erdos821.Blueprint.CandidateData in
  -- Abbreviations for the two Finsets and the maximal weight.
  set F : Finset ℕ :=
    (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => Nat.Prime (2 * u + 1)) with hFdef
  set S : Finset ℕ :=
    F.filter (fun u => C.weighted x jstar u ≠ 0) with hSdef
  set T : Finset ℕ := Erdos821.smoothShiftedPrimes δ x with hTdef
  set W : ℝ := Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) with hWdef
  have hprime_eq : C.primeMass x jstar = ∑ u ∈ F, C.weighted x jstar u := rfl
  have hSF : S ⊆ F := Finset.filter_subset _ _
  have hsum_eq : ∑ u ∈ F, C.weighted x jstar u = ∑ u ∈ S, C.weighted x jstar u := by
    symm
    apply Finset.sum_subset hSF
    intro u huF huS
    have hne : ¬ (C.weighted x jstar u ≠ 0) := by
      intro hne
      exact huS (Finset.mem_filter.mpr ⟨huF, hne⟩)
    exact not_ne_iff.mp hne
  have hsum_le : ∑ u ∈ S, C.weighted x jstar u ≤ (S.card : ℝ) * W := by
    have h := Finset.sum_le_card_nsmul S (fun u => C.weighted x jstar u) W
      (fun u _ => hup u)
    rw [nsmul_eq_mul] at h
    exact h
  have hcard_le : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun u => 2 * u + 1)
    · -- MapsTo
      intro u huS
      have huS_fin : u ∈ S := Finset.mem_coe.mp huS
      have huF : u ∈ F := hSF huS_fin
      have hprime : Nat.Prime (2 * u + 1) :=
        (Finset.mem_filter.mp huF).2
      have hwne : C.weighted x jstar u ≠ 0 :=
        (Finset.mem_filter.mp huS_fin).2
      obtain ⟨hxu, hxu2, hsmooth⟩ := hsupp u hwne
      have hmem := mem_smooth_of_support hx5 h2le hxu hxu2 hprime hsmooth
      show (2 * u + 1) ∈ (T : Set ℕ)
      rw [hTdef]
      exact Finset.mem_coe.mpr hmem
    · -- InjOn
      intro a _ b _ hab
      dsimp only at hab
      omega
  have hWnn : 0 ≤ W := le_of_lt (Real.exp_pos _)
  calc C.primeMass x jstar = ∑ u ∈ S, C.weighted x jstar u := by
          rw [hprime_eq, hsum_eq]
    _ ≤ (S.card : ℝ) * W := hsum_le
    _ ≤ (T.card : ℝ) * W := by
          apply mul_le_mul_of_nonneg_right _ hWnn
          exact_mod_cast hcard_le

end Erdos821.Count

/-- P10 elementary boundary proof: from weighted bounds and prime extraction,
inject `u ↦ 2 * u + 1` and absorb `L`-losses into `x ^ σ`. -/
theorem Erdos821.Blueprint.count_from_weighted_mass (δ : ℝ) (hδ : 0 < δ)
    (C : Erdos821.Blueprint.CandidateData)
    (hb : C.Bounds δ) (hp : Erdos821.Blueprint.PrimeExtraction C) :
    ∀ σ : ℝ, 0 < σ → ∀ᶠ x : ℝ in atTop,
      x ^ (1 - σ) ≤ ((Erdos821.smoothShiftedPrimes δ x).card : ℝ) := by
  open Erdos821.Blueprint.CandidateData in
  open Erdos821.Count in
  intro σ hσ
  rcases hb with ⟨K, CA, cmin, cmax, hK, _, _, hBounds⟩
  rcases hp with ⟨jstar, hjstar, c, hc, hPrime⟩
  have hBj := hBounds jstar hjstar
  have hAbs := Erdos821.Count.absorb K (CA + 1) σ c hK hσ hc
  have hTwo := Erdos821.Count.eventually_two_le_rpow hδ
  have hGe5 : ∀ᶠ x : ℝ in atTop, (5 : ℝ) ≤ x := Filter.eventually_ge_atTop 5
  filter_upwards [hBj, hPrime, hAbs, hTwo, hGe5] with x hB hP hA h2 h5
  rcases hB with ⟨hmass_lo, _, _, _, hup, hsupp_full⟩
  -- Simplify support to the upper smoothness bound only.
  have hsupp : ∀ u : ℕ, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x ∧
        ∀ q : ℕ, q.Prime → q ∣ u → (q : ℝ) ≤ x ^ δ := by
    intro u hu
    obtain ⟨hxu, hxu2, hs⟩ := hsupp_full u hu
    exact ⟨hxu, hxu2, fun q hq hqdvd => (hs q hq hqdvd).2⟩
  have hxpos : 0 < x := by linarith
  have hxnn : 0 ≤ x := le_of_lt hxpos
  have hLpos : 0 < Erdos821.Blueprint.Analytic.L x :=
    Real.log_pos (by linarith : (1 : ℝ) < x)
  have hLnn : 0 ≤ Erdos821.Blueprint.Analytic.L x := le_of_lt hLpos
  have hWpos : 0 < Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) :=
    Real.exp_pos _
  have hWnn : 0 ≤ Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) :=
    le_of_lt hWpos
  -- Upper bound: prime mass by smooth count times maximal weight.
  have hle1 : C.primeMass x jstar ≤
      ((Erdos821.smoothShiftedPrimes δ x).card : ℝ) *
        Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) :=
    Erdos821.Count.primeMass_le_card_mul h5 h2 hup hsupp
  -- Lower bound chain: `c * (x * L ^ (-CA)) / L ≤ card * W`.
  have hLneg : Erdos821.Blueprint.Analytic.L x ^ (-CA) =
      (Erdos821.Blueprint.Analytic.L x ^ CA)⁻¹ :=
    Real.rpow_neg hLnn CA
  have hLrpow_pos : 0 < Erdos821.Blueprint.Analytic.L x ^ CA :=
    Real.rpow_pos_of_pos hLpos CA
  have hLneg_pos : 0 < Erdos821.Blueprint.Analytic.L x ^ (-CA) :=
    Real.rpow_pos_of_pos hLpos (-CA)
  have hlow : c * (x * Erdos821.Blueprint.Analytic.L x ^ (-CA)) /
      Erdos821.Blueprint.Analytic.L x ≤
      ((Erdos821.smoothShiftedPrimes δ x).card : ℝ) *
        Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) := by
    have h1 : c * (x * Erdos821.Blueprint.Analytic.L x ^ (-CA)) ≤
        c * C.mass x jstar := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hc)
      exact hmass_lo
    have h3 : c * (x * Erdos821.Blueprint.Analytic.L x ^ (-CA)) /
        Erdos821.Blueprint.Analytic.L x ≤
        c * C.mass x jstar / Erdos821.Blueprint.Analytic.L x := by
      have hLinvnn : 0 ≤ (Erdos821.Blueprint.Analytic.L x)⁻¹ :=
        inv_nonneg.mpr (le_of_lt hLpos)
      calc c * (x * Erdos821.Blueprint.Analytic.L x ^ (-CA)) /
            Erdos821.Blueprint.Analytic.L x
          = (c * (x * Erdos821.Blueprint.Analytic.L x ^ (-CA))) *
            (Erdos821.Blueprint.Analytic.L x)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (c * C.mass x jstar) * (Erdos821.Blueprint.Analytic.L x)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 hLinvnn
        _ = c * C.mass x jstar / Erdos821.Blueprint.Analytic.L x := by
            rw [div_eq_mul_inv]
    exact le_trans h3 (le_trans hP hle1)
  -- Combine with absorption to get `x ^ (1 - σ) ≤ card`.
  have hLadd : Erdos821.Blueprint.Analytic.L x ^ (CA + 1) =
      Erdos821.Blueprint.Analytic.L x ^ CA *
        Erdos821.Blueprint.Analytic.L x := by
    have h := Real.rpow_add hLpos CA (1 : ℝ)
    rwa [Real.rpow_one] at h
  have hLadd_pos : 0 < Erdos821.Blueprint.Analytic.L x ^ (CA + 1) :=
    Real.rpow_pos_of_pos hLpos (CA + 1)
  set D : ℝ := Erdos821.Blueprint.Analytic.L x ^ (CA + 1) *
    Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) * c⁻¹ with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact mul_pos (mul_pos hLadd_pos hWpos) (inv_pos.mpr hc)
  have hDnn : 0 ≤ D := le_of_lt hDpos
  have hAle : D ≤ x ^ σ := hA
  -- `x / D ≤ card`: from `hlow` via `x / D = (c * (x * L ^ (-CA)) / L) / W`.
  have hEq : x / D =
      (c * (x * Erdos821.Blueprint.Analytic.L x ^ (-CA)) /
        Erdos821.Blueprint.Analytic.L x) /
        Real.exp (K * Real.sqrt (Erdos821.Blueprint.Analytic.L x)) := by
    rw [hDdef, hLadd, hLneg]
    field_simp
  have hxD : x / D ≤ ((Erdos821.smoothShiftedPrimes δ x).card : ℝ) := by
    rw [hEq]
    exact (div_le_iff₀ hWpos).mpr hlow
  -- `x ^ (1 - σ) = x / x ^ σ ≤ x / D`.
  have hxσpos : 0 < x ^ σ := Real.rpow_pos_of_pos hxpos σ
  have hrw : x ^ (1 - σ) = x / x ^ σ := by
    have h1 : x ^ (1 - σ) = x ^ (1 : ℝ) / x ^ σ := Real.rpow_sub hxpos 1 σ
    rwa [Real.rpow_one] at h1
  calc x ^ (1 - σ) = x / x ^ σ := hrw
    _ ≤ x / D :=
        div_le_div_of_nonneg_left hxnn hDpos hAle
    _ ≤ ((Erdos821.smoothShiftedPrimes δ x).card : ℝ) := hxD

/-- Explicit type agreement check with the blueprint interface. -/
example (δ : ℝ) (hδ : 0 < δ) (C : Erdos821.Blueprint.CandidateData)
    (hb : C.Bounds δ) (hp : Erdos821.Blueprint.PrimeExtraction C)
    (σ : ℝ) (hσ : 0 < σ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (1 - σ) ≤ ((Erdos821.smoothShiftedPrimes δ x).card : ℝ) :=
  Erdos821.Blueprint.count_from_weighted_mass δ hδ C hb hp σ hσ
