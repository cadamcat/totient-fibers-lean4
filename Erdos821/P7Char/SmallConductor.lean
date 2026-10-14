import Erdos821.P7Char.Extraction
import Erdos821.P7Char.FourierRep

/-! Small conductors: for a fixed complementary variable the extracted prime sum is
separated harmonically; the coprimality to `h` removes boundedly many primes. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory Erdos821.Blueprint.Analytic
open scoped Classical

namespace Erdos821.P7Char

open Erdos821.Blueprint

/-- Character value restricted to integers coprime to `h`. -/
def cv {Q : ℕ} (h : ℕ) (χ : CharacterIndex Q) (n : ℕ) : ℂ :=
  if Nat.Coprime n h then charValue χ n else 0

theorem charValue_mul {Q : ℕ} (χ : CharacterIndex Q) (m n : ℕ) :
    charValue χ (m * n) = charValue χ m * charValue χ n := by
  unfold charValue
  rw [Nat.cast_mul, map_mul]

theorem charValue_norm_le {Q : ℕ} (χ : CharacterIndex Q) (n : ℕ) : ‖charValue χ n‖ ≤ 1 :=
  DirichletCharacter.norm_le_one _ _

theorem cv_mul {Q : ℕ} (h : ℕ) (χ : CharacterIndex Q) (m n : ℕ) :
    cv h χ (m * n) = cv h χ m * cv h χ n := by
  unfold cv
  by_cases hm : Nat.Coprime m h
  · by_cases hn : Nat.Coprime n h
    · rw [if_pos (Nat.coprime_mul_iff_left.2 ⟨hm, hn⟩), if_pos hm, if_pos hn, charValue_mul]
    · rw [if_neg (fun H => hn (Nat.coprime_mul_iff_left.1 H).2), if_neg hn, mul_zero]
  · rw [if_neg (fun H => hm (Nat.coprime_mul_iff_left.1 H).1), if_neg hm, zero_mul]

theorem cv_norm_le {Q : ℕ} (h : ℕ) (χ : CharacterIndex Q) (n : ℕ) : ‖cv h χ n‖ ≤ 1 := by
  unfold cv
  split_ifs
  · exact charValue_norm_le χ n
  · simp

theorem twisted_eq_cv (I : Finset ℕ) (w : ℕ → ℝ) (h : ℕ) {Q : ℕ} (χ : CharacterIndex Q) :
    twisted I w h χ = ∑ u ∈ I, (w u : ℂ) * cv h χ u := by
  unfold twisted cv
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  split_ifs <;> simp

theorem harmonic_sum_continuous {Q : ℕ} (χ : CharacterIndex Q) (S : Finset ℕ) :
    Continuous (fun t => ∑ p ∈ S, charValue χ p * tw p t / (p : ℂ)) :=
  continuous_finset_sum _ (fun p _ => (continuous_const.mul (tw_continuous p)).div_const _)

/-- Small-conductor bound for one character and one `h`. -/
theorem small_twisted_bound (C : CandidateData) (x : ℝ) (hx : 0 < x) (jstar : ℕ)
    (s₀ : C.bands.Slot x)
    (hB : ∀ p ∈ C.bands.slotValues x jstar s₀,
      p.Prime ∧ S56Core.GroupFree (C.bands.groups x) p)
    (hψ : Function.support C.psi ⊆ Set.Icc 1 2) (Mψ : ℝ) (hMψ : ∀ y, |C.psi y| ≤ Mψ)
    (N₀ : ℕ) (hN : ∀ p ∈ C.bands.slotValues x jstar s₀, ⌊2 * x⌋₊ / p ≤ N₀)
    (a₂ : ℝ → ℂ) (hrep : CutoffRep (fun y => y * C.psi y) a₂)
    (Q h : ℕ) (χ : CharacterIndex Q) (cS : ℝ)
    (hcount : (((C.bands.slotValues x jstar s₀).filter (fun p => ¬ Nat.Coprime p h)).card : ℝ)
      ≤ cS)
    (T0 ε MH : ℝ) (hε : 0 ≤ ε)
    (hMH : ∀ t, ‖∑ p ∈ C.bands.slotValues x jstar s₀, charValue χ p * tw p t / (p : ℂ)‖ ≤ MH)
    (hsmall : ∀ t, ‖t‖ ≤ T0 →
      ‖∑ p ∈ C.bands.slotValues x jstar s₀, charValue χ p * tw p t / (p : ℂ)‖ ≤ ε) :
    ‖twisted (Finset.Icc 1 ⌊2 * x⌋₊) (C.weighted x jstar) h χ‖ ≤
      ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r *
        ((x / r) * (ε * (∫ t, ‖a₂ t‖) + MH * ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖) + Mψ * cS) := by
  set B0 := C.bands.slotValues x jstar s₀ with hB0
  set β := beta C.bands x jstar s₀ with hβ
  have hB0pos : ∀ p ∈ B0, 0 < p := fun p hp => (hB p hp).1.pos
  have hMψ0 : 0 ≤ Mψ := (abs_nonneg _).trans (hMψ 0)
  rw [twisted_eq_cv, weighted_sum_extract C x hx jstar s₀ hB hψ (cv h χ) (fun _ => N₀) hN]
  have hswap : (∑ p ∈ B0, ∑ r ∈ Finset.Icc 1 N₀,
      (β r : ℂ) * (C.psi ((p : ℝ) * r / x) : ℂ) * cv h χ (p * r)) =
      ∑ r ∈ Finset.Icc 1 N₀, ((β r : ℂ) * cv h χ r) *
        ∑ p ∈ B0, cv h χ p * (C.psi ((p : ℝ) * r / x) : ℂ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [cv_mul]
    ring
  rw [hswap]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => ?_))
  have hr0 : 0 < r := (Finset.mem_Icc.1 hr).1
  have hβ0 : 0 ≤ β r := beta_nonneg C.bands x jstar s₀ r
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
  have hcv : ‖cv h χ r‖ ≤ 1 := cv_norm_le h χ r
  have hinner : ‖∑ p ∈ B0, cv h χ p * (C.psi ((p : ℝ) * r / x) : ℂ)‖ ≤
      (x / r) * (ε * (∫ t, ‖a₂ t‖) + MH * ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖) + Mψ * cS := by
    have hsplit : (∑ p ∈ B0, cv h χ p * (C.psi ((p : ℝ) * r / x) : ℂ)) =
        (∑ p ∈ B0, charValue χ p * (C.psi ((p : ℝ) * r / x) : ℂ)) -
          ∑ p ∈ B0, (if Nat.Coprime p h then 0 else charValue χ p) *
            (C.psi ((p : ℝ) * r / x) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      unfold cv
      split_ifs <;> ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [harmonic_fourier C.psi a₂ hrep x hx B0 hB0pos r hr0 (fun p => charValue χ p)]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_split_bound a₂ hrep.1 _
        (((e_continuous_lin (Real.log x)).mul (tw_continuous r)).mul
          (harmonic_sum_continuous χ B0)) T0 ε MH hε
      · intro t
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_mul, e_norm, tw_norm, one_mul, one_mul]
        exact hMH t
      · intro t ht
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_mul, e_norm, tw_norm, one_mul, one_mul]
        exact hsmall t ht
    · refine (norm_sum_le _ _).trans ?_
      calc ∑ p ∈ B0, ‖(if Nat.Coprime p h then 0 else charValue χ p) *
              (C.psi ((p : ℝ) * r / x) : ℂ)‖
          ≤ ∑ p ∈ B0, (if Nat.Coprime p h then (0 : ℝ) else Mψ) := by
            apply Finset.sum_le_sum
            intro p _
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            split_ifs
            · simp
            · exact (mul_le_mul (charValue_norm_le χ p) (hMψ _) (abs_nonneg _)
                zero_le_one).trans (by rw [one_mul])
        _ = ∑ p ∈ B0, (if ¬ Nat.Coprime p h then Mψ else 0) :=
            Finset.sum_congr rfl (fun p _ => by by_cases hp : Nat.Coprime p h <;> simp [hp])
        _ = ∑ p ∈ B0.filter (fun p => ¬ Nat.Coprime p h), Mψ := (Finset.sum_filter _ _).symm
        _ = Mψ * ((B0.filter (fun p => ¬ Nat.Coprime p h)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ Mψ * cS := mul_le_mul_of_nonneg_left hcount hMψ0
  have hinner0 : 0 ≤ ‖∑ p ∈ B0, cv h χ p * (C.psi ((p : ℝ) * r / x) : ℂ)‖ := norm_nonneg _
  calc β r * ‖cv h χ r‖ * ‖∑ p ∈ B0, cv h χ p * (C.psi ((p : ℝ) * r / x) : ℂ)‖
      ≤ β r * 1 * ‖∑ p ∈ B0, cv h χ p * (C.psi ((p : ℝ) * r / x) : ℂ)‖ := by
        apply mul_le_mul_of_nonneg_right _ hinner0
        exact mul_le_mul_of_nonneg_left hcv hβ0
    _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hinner hβ0

/-- The reciprocal-totient mass of all character indices of level at most `R` is at most `R`. -/
theorem sum_inv_totient_small (Q R : ℕ) :
    ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => fC χ ≤ R), ((fC χ).totient : ℝ)⁻¹ ≤ R := by
  calc _ ≤ ∑ χ ∈ (Finset.univ : Finset (CharacterIndex Q)).filter (fun χ => fC χ ≤ R),
        ((fC χ).totient : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro χ hχ
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hχ).2⟩
        · intro _ _ _
          positivity
    _ = ∑ r : Fin Q, if r.val + 1 ≤ R then (1 : ℝ) else 0 := by
        rw [Finset.sum_filter, Fintype.sum_sigma]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        by_cases hr : r.val + 1 ≤ R
        · have hcard : Fintype.card (DirichletCharacter ℂ (r.val + 1)) = (r.val + 1).totient := by
            rw [← Nat.card_eq_fintype_card]
            exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ _
          have hφ : (0 : ℝ) < ((r.val + 1).totient : ℝ) := by
            exact_mod_cast Nat.totient_pos.2 (Nat.succ_pos _)
          have e1 : ∀ c : DirichletCharacter ℂ (r.val + 1),
              (if fC (⟨r, c⟩ : CharacterIndex Q) ≤ R then
                ((fC (⟨r, c⟩ : CharacterIndex Q)).totient : ℝ)⁻¹ else 0) =
              ((r.val + 1).totient : ℝ)⁻¹ := fun c => if_pos hr
          rw [if_pos hr, Finset.sum_congr rfl (fun c _ => e1 c), Finset.sum_const,
            Finset.card_univ, hcard, nsmul_eq_mul]
          field_simp
        · rw [if_neg hr]
          refine Finset.sum_eq_zero (fun c _ => ?_)
          exact if_neg hr
    _ = ∑ m ∈ Finset.range Q, if m + 1 ≤ R then (1 : ℝ) else 0 :=
        Fin.sum_univ_eq_sum_range (fun m => if m + 1 ≤ R then (1 : ℝ) else 0) Q
    _ ≤ ∑ m ∈ Finset.range R, (1 : ℝ) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
          omega
        · intro _ _ _
          norm_num
    _ = R := by simp

/-- At most `θ/σ` primes `p ≥ x^σ` divide `h ≤ x^θ`. -/
theorem card_large_prime_divisors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (h : ℕ) (hh : 0 < h)
    (lo : ℝ) (hlo : 1 < lo) (hSlo : ∀ p ∈ S, lo ≤ p) :
    ((S.filter (fun p => ¬ Nat.Coprime p h)).card : ℝ) ≤ Real.log h / Real.log lo := by
  set S' := S.filter (fun p => ¬ Nat.Coprime p h)
  have hdvd : ∀ p ∈ S', p ∣ h := by
    intro p hp
    obtain ⟨hpS, hpc⟩ := Finset.mem_filter.1 hp
    exact (Nat.Prime.dvd_iff_not_coprime (hS p hpS)).2 hpc
  have hprod : (∏ p ∈ S', p) ∣ h := by
    apply Finset.prod_primes_dvd
    · intro p hp; exact (hS p (Finset.mem_filter.1 hp).1).prime
    · intro p hp; exact hdvd p hp
  have hle : (∏ p ∈ S', p) ≤ h := Nat.le_of_dvd hh hprod
  have hlog : (S'.card : ℝ) * Real.log lo ≤ Real.log h := by
    calc (S'.card : ℝ) * Real.log lo = ∑ _p ∈ S', Real.log lo := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ S', Real.log (p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact Real.log_le_log (by linarith) (hSlo p (Finset.mem_filter.1 hp).1)
      _ = Real.log (∏ p ∈ S', (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact Nat.cast_ne_zero.2 (hS p (Finset.mem_filter.1 hp).1).ne_zero
      _ ≤ Real.log h := by
          apply Real.log_le_log
          · apply Finset.prod_pos
            intro p hp
            exact Nat.cast_pos.2 (hS p (Finset.mem_filter.1 hp).1).pos
          · rw [← Nat.cast_prod]
            exact Nat.cast_le.2 hle
  have hlo' : 0 < Real.log lo := Real.log_pos hlo
  rw [le_div_iff₀ hlo']
  exact hlog

end Erdos821.P7Char
