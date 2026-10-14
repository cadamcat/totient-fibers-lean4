import Erdos821.P7Char.LargeConductor

/-! Deterministic assembly for one `x`: the summed nonprincipal differences are bounded by
the small-conductor and large-conductor contributions. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory Erdos821.Blueprint.Analytic
open scoped Classical

namespace Erdos821.P7Char

open Erdos821.Blueprint

theorem deterministic_bound (C : CandidateData) (x : ℝ) (hx : 0 < x) (jstar : ℕ)
    (s₀ : C.bands.Slot x)
    (hB : ∀ p ∈ C.bands.slotValues x jstar s₀,
      p.Prime ∧ S56Core.GroupFree (C.bands.groups x) p)
    (hψ : Function.support C.psi ⊆ Set.Icc 1 2) (Mψ : ℝ) (hMψ : ∀ y, |C.psi y| ≤ Mψ)
    (a a₂ : ℝ → ℂ) (hrep : CutoffRep C.psi a) (hrep₂ : CutoffRep (fun y => y * C.psi y) a₂)
    (K : ℝ) (hK : 0 ≤ K) (hLSK : LSBound K)
    (X : ℝ) (hX : 1 ≤ X) (R : ℕ) (SH : ℝ)
    (hSH : ∑ h ∈ Erdos821.P7B.squarefreeModuli X, (h.totient : ℝ)⁻¹ ≤ SH)
    (N₀ : ℕ) (hN : ∀ p ∈ C.bands.slotValues x jstar s₀, ⌊2 * x⌋₊ / p ≤ N₀)
    (cS : ℝ) (hcS : 0 ≤ cS)
    (hcount : ∀ h ∈ Erdos821.P7B.squarefreeModuli X,
      (((C.bands.slotValues x jstar s₀).filter (fun p => ¬ Nat.Coprime p h)).card : ℝ) ≤ cS)
    (T0 ε MH : ℝ) (hε : 0 ≤ ε) (hMH0 : 0 ≤ MH)
    (hMH : ∀ χ ∈ (primitiveCharacters ⌊X⌋₊).filter (fun χ => 1 < fC χ ∧ fC χ ≤ R), ∀ t,
      ‖∑ p ∈ C.bands.slotValues x jstar s₀, charValue χ p * tw p t / (p : ℂ)‖ ≤ MH)
    (hsmall : ∀ χ ∈ (primitiveCharacters ⌊X⌋₊).filter (fun χ => 1 < fC χ ∧ fC χ ≤ R), ∀ t,
      ‖t‖ ≤ T0 →
      ‖∑ p ∈ C.bands.slotValues x jstar s₀, charValue χ p * tw p t / (p : ℂ)‖ ≤ ε)
    (βB : ℕ → ℝ)
    (hβB : ∀ k, ∑ r ∈ Finset.Icc 1 (⌊2 * x⌋₊ / 2 ^ k), (beta C.bands x jstar s₀ r) ^ 2 ≤ βB k)
    (BBmax : ℝ) (hBB0 : 0 ≤ BBmax)
    (hBB : ∀ k ∈ (C.bands.slotValues x jstar s₀).image (Nat.log 2),
      blockBB K ⌊X⌋₊ R (2 ^ (k + 1)) (⌊2 * x⌋₊ / 2 ^ k) (βB k) ≤ BBmax) :
    (∑ d ∈ oddSqfreeModuli X,
        |progressionSum C x jstar d -
          Erdos821.P7B.coprimeMass C x jstar d / (Nat.totient d : ℝ)|) ≤
      SH * ((R : ℝ) * (∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r *
          ((x / r) * (ε * (∫ t, ‖a₂ t‖) + MH * ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖) + Mψ * cS)) +
        (((C.bands.slotValues x jstar s₀).image (Nat.log 2)).card : ℝ) *
          ((∫ t, ‖a t‖) * ((((Finset.range (Nat.log 2 ⌊X⌋₊ + 1)).filter
            (fun j => R < 2 ^ (j + 1))).card : ℝ) * BBmax))) := by
  set B0 := C.bands.slotValues x jstar s₀ with hB0
  set β := beta C.bands x jstar s₀ with hβ
  set I := Finset.Icc 1 ⌊2 * x⌋₊
  set w := C.weighted x jstar
  set Q := ⌊X⌋₊ with hQdef
  have hQ : 1 ≤ Q := by rw [hQdef]; exact Nat.le_floor (by simpa using hX)
  set SB := ∑ r ∈ Finset.Icc 1 N₀, β r *
    ((x / r) * (ε * (∫ t, ‖a₂ t‖) + MH * ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖) + Mψ * cS) with hSB
  set A₁ := ∫ t, ‖a t‖
  set J := (Finset.range (Nat.log 2 Q + 1)).filter (fun j => R < 2 ^ (j + 1))
  set Ks := B0.image (Nat.log 2)
  have hMψ0 : 0 ≤ Mψ := (abs_nonneg _).trans (hMψ 0)
  have hA₁ : 0 ≤ A₁ := integral_nonneg (fun _ => norm_nonneg _)
  have htail : 0 ≤ ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖ :=
    setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => norm_nonneg _))
  have hA₂ : 0 ≤ ∫ t, ‖a₂ t‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hSB0 : 0 ≤ SB := by
    apply Finset.sum_nonneg
    intro r _
    apply mul_nonneg (beta_nonneg _ _ _ _ _)
    apply add_nonneg _ (mul_nonneg hMψ0 hcS)
    apply mul_nonneg (by positivity)
    exact add_nonneg (mul_nonneg hε hA₂) (mul_nonneg hMH0 htail)
  set Ymax := (R : ℝ) * SB + (Ks.card : ℝ) * (A₁ * ((J.card : ℝ) * BBmax)) with hYmax
  have hY0 : 0 ≤ Ymax := by positivity
  have hred := typeI_character_reduction X I w
  refine le_trans hred ?_
  have hper : ∀ h ∈ Erdos821.P7B.squarefreeModuli X,
      ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => 1 < fC χ),
        (((fC χ).totient : ℝ)⁻¹ * ‖twisted I w h χ‖) ≤ Ymax := by
    intro h hh
    set P := (primitiveCharacters Q).filter (fun χ => 1 < fC χ)
    rw [← Finset.sum_filter_add_sum_filter_not P (fun χ => fC χ ≤ R)]
    apply add_le_add
    · -- small conductors
      calc ∑ χ ∈ P.filter (fun χ => fC χ ≤ R), ((fC χ).totient : ℝ)⁻¹ * ‖twisted I w h χ‖
          ≤ ∑ χ ∈ P.filter (fun χ => fC χ ≤ R), ((fC χ).totient : ℝ)⁻¹ * SB := by
            apply Finset.sum_le_sum
            intro χ hχ
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hχ' : χ ∈ (primitiveCharacters Q).filter (fun χ => 1 < fC χ ∧ fC χ ≤ R) := by
              obtain ⟨hχP, hR⟩ := Finset.mem_filter.1 hχ
              obtain ⟨hprim, h1⟩ := Finset.mem_filter.1 hχP
              exact Finset.mem_filter.2 ⟨hprim, h1, hR⟩
            exact small_twisted_bound C x hx jstar s₀ hB hψ Mψ hMψ N₀ hN a₂ hrep₂ Q h χ cS
              (hcount h hh) T0 ε MH hε (hMH χ hχ') (hsmall χ hχ')
        _ = (∑ χ ∈ P.filter (fun χ => fC χ ≤ R), ((fC χ).totient : ℝ)⁻¹) * SB := by
            rw [Finset.sum_mul]
        _ ≤ (R : ℝ) * SB := by
            apply mul_le_mul_of_nonneg_right _ hSB0
            refine le_trans ?_ (sum_inv_totient_small Q R)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro χ hχ
              obtain ⟨hχP, hR⟩ := Finset.mem_filter.1 hχ
              exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hχP).1, hR⟩
            · intro _ _ _
              positivity
    · -- large conductors
      calc ∑ χ ∈ P.filter (fun χ => ¬ fC χ ≤ R), ((fC χ).totient : ℝ)⁻¹ * ‖twisted I w h χ‖
          ≤ ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => R < fC χ),
              ((fC χ).totient : ℝ)⁻¹ * ‖twisted I w h χ‖ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro χ hχ
              obtain ⟨hχP, hR⟩ := Finset.mem_filter.1 hχ
              exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hχP).1, not_le.1 hR⟩
            · intro _ _ _
              positivity
        _ ≤ ∑ k ∈ Ks, A₁ * ((J.card : ℝ) *
              blockBB K Q R (2 ^ (k + 1)) (⌊2 * x⌋₊ / 2 ^ k) (βB k)) :=
            large_part_bound C x hx jstar s₀ hB hψ a hrep K hK hLSK Q h R hQ βB hβB
        _ ≤ ∑ k ∈ Ks, A₁ * ((J.card : ℝ) * BBmax) := by
            apply Finset.sum_le_sum
            intro k hk
            apply mul_le_mul_of_nonneg_left _ hA₁
            exact mul_le_mul_of_nonneg_left (hBB k hk) (Nat.cast_nonneg _)
        _ = (Ks.card : ℝ) * (A₁ * ((J.card : ℝ) * BBmax)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ h ∈ Erdos821.P7B.squarefreeModuli X, (h.totient : ℝ)⁻¹ *
        ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => 1 < fC χ),
          (((fC χ).totient : ℝ)⁻¹ * ‖twisted I w h χ‖)
      ≤ ∑ h ∈ Erdos821.P7B.squarefreeModuli X, (h.totient : ℝ)⁻¹ * Ymax := by
        apply Finset.sum_le_sum
        intro h hh
        exact mul_le_mul_of_nonneg_left (hper h hh) (by positivity)
    _ = (∑ h ∈ Erdos821.P7B.squarefreeModuli X, (h.totient : ℝ)⁻¹) * Ymax := by
        rw [Finset.sum_mul]
    _ ≤ SH * Ymax := mul_le_mul_of_nonneg_right hSH hY0

end Erdos821.P7Char
