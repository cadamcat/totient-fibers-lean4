import Erdos821.P7Char.Task
import Erdos821.S56.CharacterCongruence

/-! Character orthogonality for `d ∣ 2u+1` and reduction of nonprincipal characters
modulo `d` to primitive characters modulo conductors `f ∣ d`, `f > 1`. -/
noncomputable section
open scoped BigOperators
open Filter Erdos821.Blueprint.Analytic
open scoped Classical

namespace Erdos821.P7Char

open Erdos821.Blueprint

/-- The level of a character index. -/
def fC {Q : ℕ} (χ : CharacterIndex Q) : ℕ := χ.1.val + 1

/-- Odd squarefree moduli up to `X`. -/
def oddSqfreeModuli (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun d => Odd d ∧ Squarefree d)

/-- Twisted sum with coprimality to `h`. -/
def twisted (I : Finset ℕ) (w : ℕ → ℝ) (h : ℕ) {Q : ℕ} (χ : CharacterIndex Q) : ℂ :=
  ∑ u ∈ I.filter (fun u => Nat.Coprime u h), (w u : ℂ) * charValue χ u

theorem dvd_two_mul_add_one_iff (d m' : ℕ) (hd : Odd d) (hdm : d = 2 * m' + 1) (u : ℕ) :
    d ∣ 2 * u + 1 ↔ (u : ZMod d) = (m' : ZMod d) := by
  rw [ZMod.natCast_eq_natCast_iff]
  have hg : Nat.gcd d 2 = 1 := (Nat.coprime_two_left.2 hd).symm
  constructor
  · intro h
    have h1 : 2 * u + 1 ≡ 2 * m' + 1 [MOD d] := by
      rw [← hdm]
      exact (Nat.modEq_zero_iff_dvd.2 h).trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl).symm
    have h2 : 2 * u ≡ 2 * m' [MOD d] := Nat.ModEq.add_right_cancel' 1 h1
    exact Nat.ModEq.cancel_left_of_coprime hg h2
  · intro h
    have h1 : 2 * u + 1 ≡ 2 * m' + 1 [MOD d] := (h.mul_left 2).add_right 1
    rw [← hdm] at h1
    exact Nat.modEq_zero_iff_dvd.1 (h1.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))

theorem progression_orthogonality (d : ℕ) [NeZero d] (hd : Odd d) (I : Finset ℕ) (w : ℕ → ℝ) :
    |(∑ u ∈ I.filter (fun u => d ∣ 2 * u + 1), w u) -
        (∑ u ∈ I.filter (fun u => Nat.Coprime u d), w u) / (d.totient : ℝ)| ≤
      (d.totient : ℝ)⁻¹ *
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
          ‖∑ u ∈ I, (w u : ℂ) * ψ (u : ZMod d)‖ := by
  have hd0 : d ≠ 0 := NeZero.ne d
  set m' := d / 2 with hm'def
  have hdm : d = 2 * m' + 1 := by
    obtain ⟨k, hk⟩ := hd
    omega
  have hm'cop : Nat.Coprime m' d :=
    Erdos821.P7B.coprime_of_dvd_two_mul_add_one (by rw [← hdm])
  have hm'unit : IsUnit (m' : ZMod d) := (ZMod.isUnit_iff_coprime m' d).2 hm'cop
  have hφpos : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hd0)
  have hind : ∀ u : ℕ, (if d ∣ 2 * u + 1 then (1 : ℂ) else 0) =
      (d.totient : ℂ)⁻¹ *
        ∑ ψ : DirichletCharacter ℂ d, ψ (u : ZMod d) * star (ψ (m' : ZMod d)) := by
    intro u
    by_cases hu : IsUnit (u : ZMod d)
    · have hc := Erdos821.S56.character_congruence_proved d u m' hu hm'unit
      rw [inv_mul_eq_div, ← hc]
      exact if_congr (dvd_two_mul_add_one_iff d m' hd hdm u) rfl rfl
    · have h0 : ¬ d ∣ 2 * u + 1 := fun h =>
        hu ((ZMod.isUnit_iff_coprime u d).2 (Erdos821.P7B.coprime_of_dvd_two_mul_add_one h))
      simp [h0, MulChar.map_nonunit _ hu]
  have hprin : ∀ u : ℕ, (w u : ℂ) * (1 : DirichletCharacter ℂ d) (u : ZMod d) =
      if Nat.Coprime u d then (w u : ℂ) else 0 := by
    intro u
    by_cases hu : Nat.Coprime u d
    · rw [if_pos hu, MulChar.one_apply ((ZMod.isUnit_iff_coprime u d).2 hu), mul_one]
    · rw [if_neg hu, MulChar.map_nonunit _ (fun h => hu ((ZMod.isUnit_iff_coprime u d).1 h)),
        mul_zero]
  set S : DirichletCharacter ℂ d → ℂ := fun ψ => ∑ u ∈ I, (w u : ℂ) * ψ (u : ZMod d) with hS
  have hprog : ((∑ u ∈ I.filter (fun u => d ∣ 2 * u + 1), w u : ℝ) : ℂ) =
      (d.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ d, star (ψ (m' : ZMod d)) * S ψ := by
    rw [Complex.ofReal_sum, Finset.sum_filter]
    calc
      (∑ u ∈ I, if d ∣ 2 * u + 1 then ((w u : ℝ) : ℂ) else 0) =
          ∑ u ∈ I, (w u : ℂ) * (if d ∣ 2 * u + 1 then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        split_ifs <;> simp
      _ = ∑ u ∈ I, (w u : ℂ) * ((d.totient : ℂ)⁻¹ *
            ∑ ψ : DirichletCharacter ℂ d, ψ (u : ZMod d) * star (ψ (m' : ZMod d))) := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [hind u]
      _ = (d.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ d, star (ψ (m' : ZMod d)) * S ψ := by
        simp only [hS, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ψ _ => Finset.sum_congr rfl (fun u _ => ?_))
        ring
  have hcop : ((∑ u ∈ I.filter (fun u => Nat.Coprime u d), w u : ℝ) : ℂ) = S 1 := by
    rw [Complex.ofReal_sum, Finset.sum_filter, hS]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [hprin u]
  have hsplit : (∑ ψ : DirichletCharacter ℂ d, star (ψ (m' : ZMod d)) * S ψ) =
      S 1 + ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        star (ψ (m' : ZMod d)) * S ψ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ d)),
      MulChar.one_apply hm'unit, star_one, one_mul]
  have hdiff : (((∑ u ∈ I.filter (fun u => d ∣ 2 * u + 1), w u) -
        (∑ u ∈ I.filter (fun u => Nat.Coprime u d), w u) / (d.totient : ℝ) : ℝ) : ℂ) =
      (d.totient : ℂ)⁻¹ * ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        star (ψ (m' : ZMod d)) * S ψ := by
    have hφc : (d.totient : ℂ) ≠ 0 := by exact_mod_cast hφpos.ne'
    rw [Complex.ofReal_sub, Complex.ofReal_div, hprog, hcop, hsplit, Complex.ofReal_natCast]
    field_simp
    ring
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hdiff
  simp only [Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [hnorm, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hφpos.le)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ψ _ => ?_))
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one ψ _)

/-! ### Character indices -/

theorem cast_dirichlet_apply {m n : ℕ} (h : m = n) (χ : DirichletCharacter ℂ m) (k : ℕ) :
    (cast (congrArg (DirichletCharacter ℂ) h) χ) (k : ZMod n) = χ (k : ZMod m) := by
  subst h
  rfl

theorem cast_dirichlet_conductor {m n : ℕ} (h : m = n) (χ : DirichletCharacter ℂ m) :
    (cast (congrArg (DirichletCharacter ℂ) h) χ).conductor = χ.conductor := by
  subst h
  rfl

/-- Index of a character of level `m ≤ Q`. -/
def toIdx (Q m : ℕ) (hm1 : 1 ≤ m) (hmQ : m ≤ Q) (χ : DirichletCharacter ℂ m) :
    CharacterIndex Q :=
  ⟨⟨m - 1, by omega⟩, cast (congrArg (DirichletCharacter ℂ) (by omega : m = m - 1 + 1)) χ⟩

theorem toIdx_fC (Q m : ℕ) (hm1 : 1 ≤ m) (hmQ : m ≤ Q) (χ : DirichletCharacter ℂ m) :
    fC (toIdx Q m hm1 hmQ χ) = m := by
  simp only [fC, toIdx]
  omega

theorem toIdx_apply (Q m : ℕ) (hm1 : 1 ≤ m) (hmQ : m ≤ Q) (χ : DirichletCharacter ℂ m)
    (k : ℕ) : charValue (toIdx Q m hm1 hmQ χ) k = χ (k : ZMod m) := by
  simp only [charValue, toIdx]
  exact cast_dirichlet_apply (by omega : m = m - 1 + 1) χ k

theorem toIdx_mem (Q m : ℕ) (hm1 : 1 ≤ m) (hmQ : m ≤ Q) (χ : DirichletCharacter ℂ m)
    (hχ : χ.IsPrimitive) : toIdx Q m hm1 hmQ χ ∈ primitiveCharacters Q := by
  have h : m = m - 1 + 1 := by omega
  have hp : DirichletCharacter.IsPrimitive (cast (congrArg (DirichletCharacter ℂ) h) χ) := by
    unfold DirichletCharacter.IsPrimitive at hχ ⊢
    rw [cast_dirichlet_conductor h, hχ]
    omega
  simp only [primitiveCharacters, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hp

/-- Primitive character inducing `ψ`, as an index. -/
def primIdx (Q d : ℕ) [NeZero d] (hdQ : d ≤ Q) (ψ : DirichletCharacter ℂ d) :
    CharacterIndex Q :=
  toIdx Q ψ.conductor (Nat.pos_of_ne_zero ψ.conductor_ne_zero)
    ((Nat.le_of_dvd (NeZero.pos d) ψ.conductor_dvd_level).trans hdQ) ψ.primitiveCharacter

theorem primIdx_fC (Q d : ℕ) [NeZero d] (hdQ : d ≤ Q) (ψ : DirichletCharacter ℂ d) :
    fC (primIdx Q d hdQ ψ) = ψ.conductor := toIdx_fC _ _ _ _ _

theorem primIdx_apply_coprime (Q d : ℕ) [NeZero d] (hdQ : d ≤ Q) (ψ : DirichletCharacter ℂ d)
    (n : ℕ) (hn : Nat.Coprime n d) : charValue (primIdx Q d hdQ ψ) n = ψ (n : ZMod d) := by
  rw [primIdx, toIdx_apply]
  have hInt : ψ.primitiveCharacter (((n : ℤ)) : ZMod ψ.conductor) =
      ψ ((((n : ℤ))) : ZMod d) :=
    ψ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.2 hn)
  simpa only [Int.cast_natCast] using hInt

theorem primIdx_apply_not_coprime (Q d : ℕ) [NeZero d] (hdQ : d ≤ Q)
    (ψ : DirichletCharacter ℂ d) (n : ℕ) (hn : ¬ Nat.Coprime n ψ.conductor) :
    charValue (primIdx Q d hdQ ψ) n = 0 := by
  rw [primIdx, toIdx_apply]
  exact MulChar.map_nonunit _ (fun h => hn ((ZMod.isUnit_iff_coprime n _).1 h))

theorem primIdx_injective (Q d : ℕ) [NeZero d] (hdQ : d ≤ Q) :
    Function.Injective (primIdx Q d hdQ) := by
  intro ψ₁ ψ₂ h
  apply MulChar.ext
  intro a
  have hcop : Nat.Coprime (a : ZMod d).val d := ZMod.val_coe_unit_coprime a
  have h1 := primIdx_apply_coprime Q d hdQ ψ₁ _ hcop
  have h2 := primIdx_apply_coprime Q d hdQ ψ₂ _ hcop
  rw [ZMod.natCast_zmod_val] at h1 h2
  rw [← h1, ← h2, h]

theorem character_sum_eq_twisted (I : Finset ℕ) (w : ℕ → ℝ) (Q d : ℕ) [NeZero d]
    (hdQ : d ≤ Q) (ψ : DirichletCharacter ℂ d) :
    (∑ u ∈ I, (w u : ℂ) * ψ (u : ZMod d)) =
      twisted I w (d / fC (primIdx Q d hdQ ψ)) (primIdx Q d hdQ ψ) := by
  unfold twisted
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hfd : fC (primIdx Q d hdQ ψ) ∣ d := by
    rw [primIdx_fC]; exact ψ.conductor_dvd_level
  have hdeq : d = fC (primIdx Q d hdQ ψ) * (d / fC (primIdx Q d hdQ ψ)) :=
    (Nat.mul_div_cancel' hfd).symm
  by_cases hu : Nat.Coprime u d
  · have huh : Nat.Coprime u (d / fC (primIdx Q d hdQ ψ)) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hfd) hu
    rw [if_pos huh, primIdx_apply_coprime Q d hdQ ψ u hu]
  · rw [MulChar.map_nonunit _ (fun h => hu ((ZMod.isUnit_iff_coprime u d).1 h)), mul_zero]
    split_ifs with huh
    · have hnf : ¬ Nat.Coprime u ψ.conductor := by
        intro hf
        apply hu
        rw [hdeq]
        exact Nat.Coprime.mul_right (by rwa [primIdx_fC]) huh
      rw [primIdx_apply_not_coprime Q d hdQ ψ u hnf, mul_zero]
    · rfl

theorem nonprincipal_le_primitive (I : Finset ℕ) (w : ℕ → ℝ) (Q d : ℕ) [NeZero d]
    (hdQ : d ≤ Q) :
    (∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖∑ u ∈ I, (w u : ℂ) * ψ (u : ZMod d)‖) ≤
      ∑ χ ∈ (primitiveCharacters Q).filter (fun χ => 1 < fC χ ∧ fC χ ∣ d),
        ‖twisted I w (d / fC χ) χ‖ := by
  calc
    _ = ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
          ‖twisted I w (d / fC (primIdx Q d hdQ ψ)) (primIdx Q d hdQ ψ)‖ := by
        refine Finset.sum_congr rfl (fun ψ _ => ?_)
        rw [character_sum_eq_twisted I w Q d hdQ ψ]
    _ = ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1).image
          (primIdx Q d hdQ), ‖twisted I w (d / fC χ) χ‖ := by
        rw [Finset.sum_image (fun a _ b _ hab => primIdx_injective Q d hdQ hab)]
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro χ hχ
          obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hχ
          have hψ1 : ψ ≠ 1 := (Finset.mem_erase.1 hψ).1
          have hcond1 : ψ.conductor ≠ 1 := fun h =>
            hψ1 (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)
          have hcond0 : ψ.conductor ≠ 0 := ψ.conductor_ne_zero
          refine Finset.mem_filter.2 ⟨?_, ?_, ?_⟩
          · exact toIdx_mem _ _ _ _ _ ψ.primitiveCharacter_isPrimitive
          · rw [primIdx_fC]; omega
          · rw [primIdx_fC]; exact ψ.conductor_dvd_level
        · intro _ _ _
          exact norm_nonneg _

/-- Reindexing `d = f h` over moduli divisible by a fixed `f`. -/
theorem multiples_reindex (X : ℝ) (f : ℕ) (hf : 0 < f) (G : ℕ → ℝ) (hG : ∀ h, 0 ≤ G h) :
    (∑ d ∈ (oddSqfreeModuli X).filter (fun d => f ∣ d),
        (d.totient : ℝ)⁻¹ * G (d / f)) ≤
      ∑ h ∈ Erdos821.P7B.squarefreeModuli X,
        ((f.totient : ℝ)⁻¹ * (h.totient : ℝ)⁻¹) * G h := by
  calc
    _ ≤ ∑ d ∈ (oddSqfreeModuli X).filter (fun d => f ∣ d),
          ((f.totient : ℝ)⁻¹ * ((d / f).totient : ℝ)⁻¹) * G (d / f) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hdmem, hfd⟩ := Finset.mem_filter.1 hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.1 (Finset.mem_filter.1 hdmem).1).1
        have hq0 : 0 < d / f := Nat.div_pos (Nat.le_of_dvd hd1 hfd) hf
        have hφf : (0 : ℝ) < f.totient := by exact_mod_cast Nat.totient_pos.2 hf
        have hφq : (0 : ℝ) < (d / f).totient := by exact_mod_cast Nat.totient_pos.2 hq0
        have hsup : ((f.totient * (d / f).totient : ℕ) : ℝ) ≤ (d.totient : ℝ) := by
          have := Nat.totient_super_multiplicative f (d / f)
          rw [Nat.mul_div_cancel' hfd] at this
          exact_mod_cast this
        apply mul_le_mul_of_nonneg_right _ (hG _)
        rw [← mul_inv]
        apply inv_anti₀ (by positivity)
        simpa using hsup
    _ = ∑ h ∈ ((oddSqfreeModuli X).filter (fun d => f ∣ d)).image (fun d => d / f),
          ((f.totient : ℝ)⁻¹ * (h.totient : ℝ)⁻¹) * G h := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.1 ha).2
        have hb' := (Finset.mem_filter.1 hb).2
        simp only at hab
        rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab]
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hh
          obtain ⟨hdmem, hfd⟩ := Finset.mem_filter.1 hd
          obtain ⟨hdIcc, _, hsq⟩ := Finset.mem_filter.1 hdmem
          obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.1 hdIcc
          simp only [Erdos821.P7B.squarefreeModuli, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨Nat.div_pos (Nat.le_of_dvd hd1 hfd) hf, (Nat.div_le_self d f).trans hdX⟩, ?_⟩
          exact hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hfd)
        · intro h _ _
          have : 0 ≤ (f.totient : ℝ)⁻¹ * (h.totient : ℝ)⁻¹ := by positivity
          exact mul_nonneg this (hG h)

/-- Character reduction of the summed nonprincipal Type I differences. -/
theorem typeI_character_reduction (X : ℝ) (I : Finset ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ oddSqfreeModuli X,
        |(∑ u ∈ I.filter (fun u => d ∣ 2 * u + 1), w u) -
          (∑ u ∈ I.filter (fun u => Nat.Coprime u d), w u) / (d.totient : ℝ)|) ≤
      ∑ h ∈ Erdos821.P7B.squarefreeModuli X, (h.totient : ℝ)⁻¹ *
        ∑ χ ∈ (primitiveCharacters ⌊X⌋₊).filter (fun χ => 1 < fC χ),
          (((fC χ).totient : ℝ)⁻¹ * ‖twisted I w h χ‖) := by
  set Q := ⌊X⌋₊
  set P := (primitiveCharacters Q).filter (fun χ => 1 < fC χ)
  have step1 : ∀ d ∈ oddSqfreeModuli X,
      |(∑ u ∈ I.filter (fun u => d ∣ 2 * u + 1), w u) -
          (∑ u ∈ I.filter (fun u => Nat.Coprime u d), w u) / (d.totient : ℝ)| ≤
        ∑ χ ∈ P, if fC χ ∣ d then (d.totient : ℝ)⁻¹ * ‖twisted I w (d / fC χ) χ‖ else 0 := by
    intro d hd
    obtain ⟨hdIcc, hodd, _⟩ := Finset.mem_filter.1 hd
    obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.1 hdIcc
    have : NeZero d := ⟨by omega⟩
    refine (progression_orthogonality d hodd I w).trans ?_
    refine (mul_le_mul_of_nonneg_left (nonprincipal_le_primitive I w Q d hdQ)
      (inv_nonneg.2 (Nat.cast_nonneg _))).trans (le_of_eq ?_)
    rw [Finset.mul_sum, ← Finset.sum_filter, Finset.filter_filter]
  calc
    _ ≤ ∑ d ∈ oddSqfreeModuli X, ∑ χ ∈ P,
          if fC χ ∣ d then (d.totient : ℝ)⁻¹ * ‖twisted I w (d / fC χ) χ‖ else 0 :=
        Finset.sum_le_sum step1
    _ = ∑ χ ∈ P, ∑ d ∈ (oddSqfreeModuli X).filter (fun d => fC χ ∣ d),
          (d.totient : ℝ)⁻¹ * ‖twisted I w (d / fC χ) χ‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [Finset.sum_filter]
    _ ≤ ∑ χ ∈ P, ∑ h ∈ Erdos821.P7B.squarefreeModuli X,
          (((fC χ).totient : ℝ)⁻¹ * (h.totient : ℝ)⁻¹) * ‖twisted I w h χ‖ := by
        apply Finset.sum_le_sum
        intro χ _
        exact multiples_reindex X (fC χ) (Nat.succ_pos _) (fun h => ‖twisted I w h χ‖)
          (fun h => norm_nonneg _)
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        ring

end Erdos821.P7Char
