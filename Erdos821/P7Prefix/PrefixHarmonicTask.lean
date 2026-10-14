import Erdos821.P7.PrefixHarmonicTask
import Erdos821.P7Band.Dyadic
import Erdos821.S56.HarmonicQBound
import PrimeNumberTheoremAnd.Erdos970.MertensClassical

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Prefix
open Erdos821.Blueprint Erdos821.Blueprint.Analytic
open Erdos821.P7Core
open Erdos970.Mertens

def primeInterval (a b y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp (a * y)⌋₊ ⌊Real.exp (b * y)⌋₊).filter Nat.Prime

theorem primeInterval_sum_eq (a b y : ℝ) (ha : 0 < a) (hab : a < b) (hy : 0 < y) :
    (∑ p ∈ primeInterval a b y, (p : ℝ)⁻¹) =
      Real.log (b / a) + E₂p (Real.exp (b * y)) - E₂p (Real.exp (a * y)) := by
  let lo := Real.exp (a * y)
  let hi := Real.exp (b * y)
  have hlohi : lo ≤ hi := Real.exp_le_exp.mpr (by nlinarith)
  have hfl : ⌊lo⌋₊ ≤ ⌊hi⌋₊ := Nat.floor_le_floor hlohi
  have hsplit : (∑ p ∈ primeInterval a b y, (p : ℝ)⁻¹) =
      (∑ p ∈ Finset.Ioc 0 ⌊hi⌋₊ with p.Prime, (1 : ℝ) / p) -
        ∑ p ∈ Finset.Ioc 0 ⌊lo⌋₊ with p.Prime, (1 : ℝ) / p := by
    rw [primeInterval, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
    simp_rw [one_div]
    ring
  have hlogs : Real.log (Real.log hi) - Real.log (Real.log lo) = Real.log (b / a) := by
    simp only [hi, lo, Real.log_exp]
    rw [← Real.log_div (mul_pos (lt_trans ha hab) hy).ne'
      (mul_pos ha hy).ne']
    congr 1
    field_simp
  rw [hsplit, sum_prime_div_eq, sum_prime_div_eq]
  calc
    _ = (Real.log (Real.log hi) - Real.log (Real.log lo)) +
        E₂p hi - E₂p lo := by ring
    _ = _ := by rw [hlogs]

theorem primeInterval_mass_eventually_lower (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ y : ℝ in atTop,
      Real.log (b / a) / 2 ≤ ∑ p ∈ primeInterval a b y, (p : ℝ)⁻¹ := by
  have hb : 0 < b := lt_trans ha hab
  have hratio : 1 < b / a := (lt_div_iff₀ ha).2 (by nlinarith)
  have hlog : 0 < Real.log (b / a) := Real.log_pos hratio
  have hE : Tendsto E₂p atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp E₂p.bound'
  have hEa : Tendsto (fun y : ℝ => E₂p (Real.exp (a * y))) atTop (nhds 0) := by
    apply hE.comp
    exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
  have hEb : Tendsto (fun y : ℝ => E₂p (Real.exp (b * y))) atTop (nhds 0) := by
    apply hE.comp
    exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  have hea : ∀ᶠ y : ℝ in atTop, |E₂p (Real.exp (a * y))| < Real.log (b / a) / 4 := by
    have h := (Metric.tendsto_nhds.mp hEa) (Real.log (b / a) / 4) (by positivity)
    simpa only [Real.dist_eq, sub_zero] using h
  have heb : ∀ᶠ y : ℝ in atTop, |E₂p (Real.exp (b * y))| < Real.log (b / a) / 4 := by
    have h := (Metric.tendsto_nhds.mp hEb) (Real.log (b / a) / 4) (by positivity)
    simpa only [Real.dist_eq, sub_zero] using h
  filter_upwards [hea, heb, eventually_gt_atTop (0 : ℝ)] with y hya hyb hy
  rw [primeInterval_sum_eq a b y ha hab hy]
  rw [abs_lt] at hya hyb
  linarith

theorem filtered_tuple_harmonic_factorization (D : BandData) (x : ℝ) (jstar : ℕ)
    (P : D.Slot x → ℕ → Prop) :
    (∑ z : D.Lists x jstar,
      if ∀ t, P t ((z t).val) then (D.listProduct z : ℝ)⁻¹ else 0) =
      ∏ t : D.Slot x,
        ∑ v ∈ D.slotValues x jstar t,
          if P t v then (v : ℝ)⁻¹ else 0 := by
  classical
  calc
    _ = ∑ z : D.Lists x jstar,
        ∏ t : D.Slot x, (if P t ((z t).val) then ((z t).val : ℝ)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hgood : ∀ t, P t ((z t).val)
      · have hinv : (D.listProduct z : ℝ)⁻¹ =
            ∏ t : D.Slot x, ((z t).val : ℝ)⁻¹ := by
          simp only [BandData.listProduct, Nat.cast_prod, Finset.prod_inv_distrib]
        have hprod :
            (∏ t : D.Slot x,
              (if P t ((z t).val) then ((z t).val : ℝ)⁻¹ else 0)) =
              ∏ t : D.Slot x, ((z t).val : ℝ)⁻¹ := by
          apply Finset.prod_congr rfl
          intro t ht
          simp [hgood t]
        simp only [if_pos hgood]
        rw [hinv, hprod]
      · obtain ⟨t, ht⟩ := not_forall.mp hgood
        have hzero :
            (∏ t' : D.Slot x,
              (if P t' ((z t').val) then ((z t').val : ℝ)⁻¹ else 0)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])
        simp only [if_neg hgood]
        rw [hzero]
    _ = ∏ t : D.Slot x,
        ∑ v : D.SlotValue x jstar t,
          if P t v.val then (v.val : ℝ)⁻¹ else 0 :=
      (Fintype.prod_sum
        (fun t (v : D.SlotValue x jstar t) =>
          if P t v.val then (v.val : ℝ)⁻¹ else 0)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro t ht
      exact Finset.sum_coe_sort (D.slotValues x jstar t)
        (fun v : ℕ => if P t v then (v : ℝ)⁻¹ else 0)

def prefixSlotCondition (C : CandidateData) (epsilon : ℝ)
    {x : ℝ} (s t : C.bands.Slot x) (p : ℕ) : Prop :=
  t = s ∨ C.prefixLen < t.1.val ∨
    |Real.log p - (C.bands.c₁ + C.bands.c₂) / 2 * C.bands.scale x t.1.val| ≤
      epsilon * C.bands.scale x t.1.val

def restrictedPrefixSlot (C : CandidateData) {x : ℝ}
    (s t : C.bands.Slot x) : Prop :=
  t ≠ s ∧ t.1.val ≤ C.prefixLen

theorem prefixMidpointEvent_iff (C : CandidateData) (epsilon : ℝ)
    {x : ℝ} {jstar : ℕ} (s : C.bands.Slot x) (z : C.bands.Lists x jstar) :
    prefixMidpointEvent C epsilon s z ↔
      ∀ t, prefixSlotCondition C epsilon s t ((z t).val) := by
  constructor
  · intro he t
    by_cases hts : t = s
    · simp [prefixSlotCondition, hts]
    by_cases hpre : C.prefixLen < t.1.val
    · simp [prefixSlotCondition, hts, hpre]
    · have hle : t.1.val ≤ C.prefixLen := Nat.le_of_not_gt hpre
      have hv := he t hts hle
      simp [prefixSlotCondition, hts, hpre, hv]
  · intro hp t hts hle
    have hv := hp t
    simpa [prefixSlotCondition, hts, not_lt_of_ge hle] using hv

theorem restrictedPrefixSlot_card_le (C : CandidateData) (x : ℝ)
    (s : C.bands.Slot x) :
    (Finset.univ.filter (restrictedPrefixSlot C s)).card ≤
      (C.prefixLen + 1) * C.bands.r₀ := by
  classical
  let P : C.bands.Slot x → Prop := fun t => t.1.val ≤ C.prefixLen
  let e : {t : C.bands.Slot x // P t} ↪ Fin (C.prefixLen + 1) × Fin C.bands.r₀ :=
    ⟨fun t => (⟨t.val.1.val, Nat.lt_succ_of_le t.property⟩, t.val.2), by
      intro a b h
      have h₁ : a.val.1.val = b.val.1.val := by
        have hh := congrArg
          (fun q : Fin (C.prefixLen + 1) × Fin C.bands.r₀ => q.1.val) h
        simpa using hh
      have h₂ : a.val.2 = b.val.2 := by
        have hh := congrArg
          (fun q : Fin (C.prefixLen + 1) × Fin C.bands.r₀ => q.2) h
        simpa using hh
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        exact h₁
      · exact h₂⟩
  have hcardP : (Finset.univ.filter P).card ≤
      (C.prefixLen + 1) * C.bands.r₀ := by
    have hcard := Fintype.card_le_of_injective e e.injective
    have heq : Fintype.card {t : C.bands.Slot x // P t} =
        (Finset.univ.filter P).card := by
      apply Fintype.card_of_subtype (Finset.univ.filter P)
      intro t
      simp [P]
    rw [heq] at hcard
    simpa [Fintype.card_prod] using hcard
  have hsub : Finset.univ.filter (restrictedPrefixSlot C s) ⊆ Finset.univ.filter P := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ht.2
  exact (Finset.card_le_card hsub).trans hcardP

theorem PrefixHarmonicTask_proof : Erdos821.P7Core.PrefixHarmonicTask := by
  intro hc δ C hC epsilon hepsilon hepsilonBand
  rcases hC with ⟨hD, hc₁, hc₂, hratio, hs', hδ, hscaleEventually,
    hprefix, hrest⟩
  let D := C.bands
  let mid : ℝ := (D.c₁ + D.c₂) / 2
  let a : ℝ := mid - epsilon
  let b : ℝ := mid + epsilon
  have hwidth : 0 < D.c₂ - D.c₁ := sub_pos.mpr hD.2.2.1
  have hc₁a : D.c₁ < a := by
    dsimp [a, mid]
    linarith
  have hb₂ : b < D.c₂ := by
    dsimp [b, mid]
    linarith
  have ha : 0 < a := (hD.2.1.trans hc₁a)
  have hab : a < b := by
    dsimp [a, b]
    linarith
  have hmpos : 0 < Real.log (b / a) / 2 := by
    have hratio' : 1 < b / a := (lt_div_iff₀ ha).2 (by linarith)
    exact half_pos (Real.log_pos hratio')
  let m : ℝ := Real.log (b / a) / 2
  have hmEvent : ∀ᶠ y : ℝ in atTop,
      m ≤ ∑ p ∈ primeInterval a b y, (p : ℝ)⁻¹ := by
    simpa [m] using primeInterval_mass_eventually_lower a b ha hab
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hmEvent
  obtain ⟨M, hM, hband⟩ :=
    Erdos821.S56Core.band_harmonic_uniform hc D hD
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let rho : ℝ := D.s' / (2 : ℝ) ^ C.prefixLen
  have hrho : 0 < rho := div_pos hD.2.2.2.1 (by positivity)
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have hYx : ∀ᶠ x : ℝ in atTop, Y ≤ rho * L x :=
    (hL.const_mul_atTop hrho).eventually_ge_atTop Y
  have hLpos : ∀ᶠ x : ℝ in atTop, 0 < L x :=
    hL.eventually_gt_atTop 0
  have hprefixScale : ∀ᶠ x : ℝ in atTop,
      ∀ i ≤ C.prefixLen, Y ≤ D.scale x i := by
    filter_upwards [hYx, hLpos] with x hYx hLx i hi
    have hpow : (2 : ℝ) ^ i ≤ 2 ^ C.prefixLen :=
      pow_le_pow_right₀ (by norm_num) hi
    have hdiv := div_le_div_of_nonneg_left
      (mul_nonneg (le_of_lt hD.2.2.2.1) hLx.le) (by positivity : 0 < (2 : ℝ) ^ i) hpow
    have hscaleEq : D.scale x i = D.s' * L x / (2 : ℝ) ^ i := by
      change C.bands.s' * L x / C.bands.ratio ^ i =
        C.bands.s' * L x / (2 : ℝ) ^ i
      rw [hratio]
    calc
      Y ≤ rho * L x := hYx
      _ = D.s' * L x / (2 : ℝ) ^ C.prefixLen := by dsimp [rho]; ring
      _ ≤ D.s' * L x / (2 : ℝ) ^ i := hdiv
      _ = D.scale x i := hscaleEq.symm
  let alpha : ℝ := min 1 (m / M)
  have halphaPos : 0 < alpha := lt_min (by norm_num) (div_pos hmpos hMpos)
  have halpha1 : alpha ≤ 1 := min_le_left _ _
  have halphaM : alpha ≤ m / M := min_le_right _ _
  let N : ℕ := (C.prefixLen + 1) * D.r₀
  let c : ℝ := alpha ^ N
  have hcpos : 0 < c := pow_pos halphaPos _
  refine ⟨c, hcpos, ?_⟩
  intro jstar hjstar
  filter_upwards [hprefixScale, hband, hLpos] with x hxScale hxband hxL
  intro s hs₁ hs₂
  let R : D.Slot x → Prop := restrictedPrefixSlot C s
  let A : D.Slot x → ℝ := fun t =>
    Erdos821.S56Core.reciprocalMass (D.slotValues x jstar t)
  let B : D.Slot x → ℝ := fun t =>
    ∑ v ∈ D.slotValues x jstar t,
      if prefixSlotCondition C epsilon s t v then (v : ℝ)⁻¹ else 0
  have hA_nonneg (t : D.Slot x) : 0 ≤ A t := by
    unfold A Erdos821.S56Core.reciprocalMass
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hrestrictedMass (t : D.Slot x) (ht : R t) : m ≤ B t := by
    change t ≠ s ∧ t.1.val ≤ C.prefixLen at ht
    rcases ht with ⟨hts, htindex⟩
    have hindex_lt : t.1.val < jstar := by omega
    have hindex_ne : t.1.val ≠ jstar := by omega
    have hslotValues : D.slotValues x jstar t = D.band x t.1.val := by
      simp [BandData.slotValues, hindex_ne]
    let y : ℝ := D.scale x t.1.val
    have hypos : 0 < y := by
      dsimp [y]
      exact Erdos821.S56Core.scale_pos D hD x hxL (t.1.val)
    have hylarge : Y ≤ y := by
      exact hxScale t.1.val htindex
    have hIoc : ∀ p, p ∈ primeInterval a b y →
        prefixSlotCondition C epsilon s t p ∧ p ∈ D.slotValues x jstar t := by
      intro p hp
      change p ∈ (Finset.Ioc ⌊Real.exp (a * y)⌋₊ ⌊Real.exp (b * y)⌋₊).filter
        Nat.Prime at hp
      simp only [Finset.mem_filter, Finset.mem_Ioc,
        Nat.floor_lt (Real.exp_pos _).le,
        Nat.le_floor_iff (Real.exp_pos _).le] at hp
      obtain ⟨hinterval, hprime⟩ := hp
      obtain ⟨hplower, hpupper⟩ := hinterval
      have hpPos : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos hprime)
      have hloglower : a * y < Real.log (p : ℝ) :=
        by simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hplower
      have hlogupper : Real.log (p : ℝ) ≤ b * y :=
        by simpa only [Real.log_exp] using Real.log_le_log hpPos hpupper
      have haExpand : a * y = mid * y - epsilon * y := by
        dsimp [a, mid]
        ring
      have hbExpand : b * y = mid * y + epsilon * y := by
        dsimp [b, mid]
        ring
      have hmidpoint :
          |Real.log (p : ℝ) - mid * y| ≤ epsilon * y := by
        apply abs_le.mpr
        constructor <;> linarith
      have hcondition : prefixSlotCondition C epsilon s t p := by
        right
        right
        simpa [y] using hmidpoint
      have hbandLower : Real.exp (D.c₁ * y) ≤ (p : ℝ) := by
        have hle := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hc₁a.le hypos.le)
        exact hle.trans hplower.le
      have hbandUpper : (p : ℝ) ≤ Real.exp (D.c₂ * y) := by
        exact hpupper.trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hb₂.le hypos.le))
      have hpband : p ∈ D.band x t.1.val := by
        change p ∈ (Finset.Icc ⌈Real.exp (D.c₁ * y)⌉₊
          ⌊Real.exp (D.c₂ * y)⌋₊).filter Nat.Prime
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.ceil_le.mpr hbandLower,
          (Nat.le_floor_iff (Real.exp_pos _).le).mpr hbandUpper⟩, hprime⟩
      have hpSlot : p ∈ D.slotValues x jstar t := by
        rw [hslotValues]
        exact hpband
      exact ⟨hcondition, hpSlot⟩
    have hsumEq :
        (∑ p ∈ primeInterval a b y, (p : ℝ)⁻¹) =
          ∑ p ∈ primeInterval a b y,
            if prefixSlotCondition C epsilon s t p then (p : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [(hIoc p hp).1]
    have hsumle :
        (∑ p ∈ primeInterval a b y,
          if prefixSlotCondition C epsilon s t p then (p : ℝ)⁻¹ else 0) ≤ B t := by
      unfold B
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (s := primeInterval a b y) (t := D.slotValues x jstar t)
        (fun p hp => (hIoc p hp).2)
      intro p hp hpn
      by_cases hcond : prefixSlotCondition C epsilon s t p
      · simp [hcond]
      · simp [hcond]
    exact (hY y hylarge).trans (by simpa [hsumEq] using hsumle)
  have hA_upper (t : D.Slot x) (ht : R t) : A t ≤ M := by
    change t ≠ s ∧ t.1.val ≤ C.prefixLen at ht
    have hindex_ne : t.1.val ≠ jstar := by omega
    have hslotValues : D.slotValues x jstar t = D.band x t.1.val := by
      simp [BandData.slotValues, hindex_ne]
    have hj : t.1.val ≤ D.last x := Nat.le_of_lt_succ t.1.isLt
    simpa [A, hslotValues] using hxband t.1.val hj
  have hB_eq_A (t : D.Slot x) (ht : ¬ R t) : B t = A t := by
    change ¬(t ≠ s ∧ t.1.val ≤ C.prefixLen) at ht
    have hout : t = s ∨ C.prefixLen < t.1.val := by
      rcases not_and_or.mp ht with heq | hgt
      · left
        by_contra hne
        exact heq hne
      · exact Or.inr (lt_of_not_ge hgt)
    have hcond (v : ℕ) : prefixSlotCondition C epsilon s t v := by
      rcases hout with heq | hgt
      · exact Or.inl heq
      · exact Or.inr (Or.inl hgt)
    unfold A B Erdos821.S56Core.reciprocalMass
    simp [hcond]
  have hfactor (t : D.Slot x) :
      (if R t then alpha else 1) * A t ≤ B t := by
    by_cases ht : R t
    · have hupper := hA_upper t ht
      have hlower := hrestrictedMass t ht
      calc
        (if R t then alpha else 1) * A t = alpha * A t := by simp [ht]
        _ ≤ alpha * M := mul_le_mul_of_nonneg_left hupper halphaPos.le
        _ ≤ m := (le_div_iff₀ hMpos).mp halphaM
        _ ≤ B t := hlower
    · simpa [ht, hB_eq_A t ht]
  have hprodLower :
      c * (∏ t : D.Slot x, A t) ≤ ∏ t : D.Slot x, B t := by
    have hcard := restrictedPrefixSlot_card_le C x s
    have hpow : alpha ^ N ≤ alpha ^ (Finset.univ.filter R).card :=
      pow_le_pow_of_le_one halphaPos.le halpha1 (by simpa [N, R] using hcard)
    have heqProd :
        (∏ t : D.Slot x, (if R t then alpha else 1) * A t) =
          alpha ^ (Finset.univ.filter R).card * ∏ t : D.Slot x, A t := by
      rw [Finset.prod_mul_distrib]
      rw [Finset.prod_ite (s := Finset.univ) (p := R)
        (fun _ : D.Slot x => alpha) (fun _ => (1 : ℝ))]
      simp only [Finset.prod_const, Finset.card_univ, one_pow, mul_one]
    calc
      c * (∏ t : D.Slot x, A t) = alpha ^ N * ∏ t : D.Slot x, A t := rfl
      _ ≤ alpha ^ (Finset.univ.filter R).card * ∏ t : D.Slot x, A t :=
        mul_le_mul_of_nonneg_right hpow (Finset.prod_nonneg (fun t _ => hA_nonneg t))
      _ = ∏ t : D.Slot x, (if R t then alpha else 1) * A t := heqProd.symm
      _ ≤ ∏ t : D.Slot x, B t := by
        apply Finset.prod_le_prod₀
        · intro t ht
          by_cases hRt : R t
          · simpa [hRt] using mul_nonneg halphaPos.le (hA_nonneg t)
          · simpa [hRt] using hA_nonneg t
        · intro t ht
          exact hfactor t
  have hfull :
      (∑ z : D.Lists x jstar, (D.listProduct z : ℝ)⁻¹) =
        ∏ t : D.Slot x, A t := by
    rw [Erdos821.S56Core.tuple_harmonic_factorization]
    rfl
  have hevent :
      (∑ z : D.Lists x jstar,
        if prefixMidpointEvent C epsilon s z then (D.listProduct z : ℝ)⁻¹ else 0) =
        ∏ t : D.Slot x, B t := by
    calc
      _ = ∑ z : D.Lists x jstar,
          if (∀ t, prefixSlotCondition C epsilon s t ((z t).val)) then
            (D.listProduct z : ℝ)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases he : prefixMidpointEvent C epsilon s z
        · have hall := (prefixMidpointEvent_iff C epsilon s z).mp he
          simp [he, hall]
        · have hnot : ¬ ∀ t, prefixSlotCondition C epsilon s t ((z t).val) := by
            intro hall
            exact he ((prefixMidpointEvent_iff C epsilon s z).mpr hall)
          by_cases hall : ∀ t, prefixSlotCondition C epsilon s t ((z t).val)
          · exact (hnot hall).elim
          · have hzero :
                (if prefixMidpointEvent C epsilon s z then
                  (D.listProduct z : ℝ)⁻¹ else 0) = 0 := by simp [he]
            rw [hzero]
            by_cases hall' : ∀ t, prefixSlotCondition C epsilon s t ((z t).val)
            · exact (hnot hall').elim
            · rw [if_neg hall']
      _ = ∏ t : D.Slot x,
          ∑ v ∈ D.slotValues x jstar t,
            if prefixSlotCondition C epsilon s t v then (v : ℝ)⁻¹ else 0 :=
        filtered_tuple_harmonic_factorization D x jstar (prefixSlotCondition C epsilon s)
      _ = ∏ t : D.Slot x, B t := rfl
  calc
    c * (∑ z : D.Lists x jstar, (D.listProduct z : ℝ)⁻¹) =
        c * ∏ t : D.Slot x, A t := by rw [hfull]
    _ ≤ ∏ t : D.Slot x, B t := hprodLower
    _ = ∑ z : D.Lists x jstar,
        if prefixMidpointEvent C epsilon s z then (D.listProduct z : ℝ)⁻¹ else 0 :=
      hevent.symm

end Erdos821.P7Prefix

end

