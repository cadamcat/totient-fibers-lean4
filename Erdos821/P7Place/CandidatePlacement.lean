import Erdos821.P7.PlacementTask
import Erdos821.S56.GeometricScales
import Erdos821.S56.SplittingScale

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Place
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

lemma scale_succ (D : BandData) (x : ℝ) (n : ℕ) (hratio : D.ratio = 2) :
    D.scale x (n + 1) = D.scale x n / 2 := by
  simp [BandData.scale, hratio, pow_succ]
  ring

lemma sum_scale_range (D : BandData) (x : ℝ) (n : ℕ) (hratio : D.ratio = 2) :
    (∑ k ∈ Finset.range (n + 1), D.scale x k) = 2 * D.scale x 0 - D.scale x n := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih, scale_succ D x n hratio]
      ring

lemma sum_scale_Icc (D : BandData) (x : ℝ) (n : ℕ) (hratio : D.ratio = 2) :
    (∑ k ∈ Finset.Icc 0 n, D.scale x k) = 2 * D.scale x 0 - D.scale x n := by
  have hset : Finset.Icc 0 n = Finset.range (n + 1) := by
    ext k
    simp
  rw [hset]
  exact sum_scale_range D x n hratio

lemma slot_scale_tail_sum (D : BandData) (x : ℝ) (j : ℕ) (hc₂ : D.c₂ ≠ 0) :
    (∑ s ∈ Finset.univ.filter (fun s : D.Slot x => j ≤ s.1.val),
      D.scale x s.1.val) =
        (D.r₀ : ℝ) * ∑ k ∈ Finset.Icc j (D.last x), D.scale x k := by
  have h := Erdos821.S56Core.all_slot_scale_sum D x j
  have hfactor : D.c₂ *
      (∑ s ∈ Finset.univ.filter (fun s : D.Slot x => j ≤ s.1.val),
        D.scale x s.1.val) =
      ∑ s ∈ Finset.univ.filter (fun s : D.Slot x => j ≤ s.1.val),
        D.c₂ * D.scale x s.1.val := by
    rw [Finset.mul_sum]
  calc
    _ = (D.c₂)⁻¹ *
        (∑ s ∈ Finset.univ.filter (fun s : D.Slot x => j ≤ s.1.val),
          D.c₂ * D.scale x s.1.val) := by
      rw [← hfactor]
      simp [hc₂]
    _ = (D.c₂)⁻¹ * ((D.r₀ : ℝ) * D.c₂ *
        ∑ k ∈ Finset.Icc j (D.last x), D.scale x k) := by rw [h]
    _ = _ := by field_simp [hc₂]

lemma full_midpoint_sum (D : BandData) (hD : D.Valid) (x : ℝ)
    (hratio : D.ratio = 2)
    (hs' : D.s' = 1 / ((D.r₀ : ℝ) * (D.c₁ + D.c₂))) :
    (∑ s : D.Slot x, (D.c₁ + D.c₂) / 2 * D.scale x s.1.val) =
      L x - (D.r₀ : ℝ) * ((D.c₁ + D.c₂) / 2) * D.scale x (D.last x) := by
  let m : ℝ := (D.c₁ + D.c₂) / 2
  have hr₀ : (0 : ℝ) < (D.r₀ : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp hD.1)
  have hc₁ : 0 < D.c₁ := hD.2.1
  have hc₂pos : 0 < D.c₂ := hc₁.trans hD.2.2.1
  have hc₂ : D.c₂ ≠ 0 := hc₂pos.ne'
  have hcsum : 0 < D.c₁ + D.c₂ := by linarith
  have hden : (D.r₀ : ℝ) * (D.c₁ + D.c₂) ≠ 0 :=
    (mul_pos hr₀ hcsum).ne'
  have hcoef : (D.r₀ : ℝ) * m * D.s' = 1 / 2 := by
    dsimp [m]
    rw [hs']
    field_simp [hden]
  have hfilter :
      Finset.univ.filter (fun s : D.Slot x => 0 ≤ s.1.val) = Finset.univ := by
    ext s
    simp
  have hslot := slot_scale_tail_sum D x 0 hc₂
  rw [hfilter] at hslot
  have hslot' :
      (∑ s : D.Slot x, D.scale x s.1.val) =
        (D.r₀ : ℝ) * ∑ k ∈ Finset.Icc 0 (D.last x), D.scale x k := by
    simpa using hslot
  have hscale0 : D.scale x 0 = D.s' * L x := by
    simp [BandData.scale]
  calc
    _ = m * (∑ s : D.Slot x, D.scale x s.1.val) := by
      dsimp [m]
      rw [Finset.mul_sum]
    _ = m * ((D.r₀ : ℝ) *
        ∑ k ∈ Finset.Icc 0 (D.last x), D.scale x k) := by rw [hslot']
    _ = m * ((D.r₀ : ℝ) *
        (2 * D.scale x 0 - D.scale x (D.last x))) := by
      rw [sum_scale_Icc D x (D.last x) hratio]
    _ = 2 * ((D.r₀ : ℝ) * m * D.s') * L x -
        (D.r₀ : ℝ) * m * D.scale x (D.last x) := by
      rw [hscale0]
      ring
    _ = L x - (D.r₀ : ℝ) * m * D.scale x (D.last x) := by
      rw [hcoef]
      ring

lemma all_slot_scale_sum_le (D : BandData) (hD : D.Valid) (x : ℝ)
    (hL : 0 < L x) (hratio : D.ratio = 2) :
    (∑ s : D.Slot x, D.scale x s.1.val) ≤
      2 * (D.r₀ : ℝ) * D.scale x 0 := by
  have hc₁ : 0 < D.c₁ := hD.2.1
  have hc₂ : 0 < D.c₂ := hc₁.trans hD.2.2.1
  have hfilter :
      Finset.univ.filter (fun s : D.Slot x => 0 ≤ s.1.val) = Finset.univ := by
    ext s
    simp
  have hsum := slot_scale_tail_sum D x 0 hc₂.ne'
  rw [hfilter] at hsum
  have hsum' :
      (∑ s : D.Slot x, D.scale x s.1.val) =
        (D.r₀ : ℝ) * ∑ k ∈ Finset.Icc 0 (D.last x), D.scale x k := by
    simpa using hsum
  have hlast := Erdos821.S56Core.scale_pos D hD x hL (D.last x)
  have hr₀ : (0 : ℝ) ≤ (D.r₀ : ℝ) := by exact_mod_cast Nat.zero_le D.r₀
  calc
    _ = (D.r₀ : ℝ) * (2 * D.scale x 0 - D.scale x (D.last x)) := by
      rw [hsum', sum_scale_Icc D x (D.last x) hratio]
    _ ≤ (D.r₀ : ℝ) * (2 * D.scale x 0) :=
      mul_le_mul_of_nonneg_left (by linarith [hlast.le]) hr₀
    _ = 2 * (D.r₀ : ℝ) * D.scale x 0 := by ring

lemma tail_slot_scale_sum_le (D : BandData) (hD : D.Valid) (x : ℝ)
    (hL : 0 < L x) (j : ℕ) (hratio : D.ratio = 2) :
    (∑ s ∈ Finset.univ.filter (fun s : D.Slot x => j < s.1.val),
      D.scale x s.1.val) ≤ (D.r₀ : ℝ) * D.scale x j := by
  have hc₁ : 0 < D.c₁ := hD.2.1
  have hc₂ : 0 < D.c₂ := hc₁.trans hD.2.2.1
  have hset :
      Finset.univ.filter (fun s : D.Slot x => j < s.1.val) =
        Finset.univ.filter (fun s : D.Slot x => j + 1 ≤ s.1.val) := by
    ext s
    simp
  rw [hset, slot_scale_tail_sum D x (j + 1) hc₂.ne']
  have hr₀ : (0 : ℝ) ≤ (D.r₀ : ℝ) := by exact_mod_cast Nat.zero_le D.r₀
  calc
    _ ≤ (D.r₀ : ℝ) *
        (D.scale x (j + 1) / (1 - D.ratio⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ hr₀
      exact Erdos821.S56Core.scale_tail_bound D hD x hL (j + 1) (D.last x)
    _ = (D.r₀ : ℝ) * D.scale x j := by
      rw [scale_succ D x j hratio, hratio]
      rw [show (1 : ℝ) - (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      field_simp

lemma tail_deviation_budget (D : BandData) (hD : D.Valid) (x : ℝ)
    (hL : 0 < L x) (j : ℕ) (hratio : D.ratio = 2)
    (hgeom : 2 * (D.r₀ : ℝ) * D.c₂ * D.s' / 2 ^ (j + 1) <
      (D.c₂ - D.c₁) * D.s' / 24) :
    D.c₂ * (∑ s ∈ Finset.univ.filter (fun s : D.Slot x => j < s.1.val),
      D.scale x s.1.val) <
        (D.c₂ - D.c₁) / 24 * D.scale x 0 := by
  have hc₁ : 0 < D.c₁ := hD.2.1
  have hc₂ : 0 < D.c₂ := hc₁.trans hD.2.2.1
  have hs' : 0 < D.s' := hD.2.2.2.1
  have hgeom' : (D.r₀ : ℝ) * D.c₂ * D.s' / 2 ^ j <
      (D.c₂ - D.c₁) * D.s' / 24 := by
    calc
      _ = 2 * (D.r₀ : ℝ) * D.c₂ * D.s' / 2 ^ (j + 1) := by
        rw [pow_succ]
        ring
      _ < _ := hgeom
  have hgeomL := mul_lt_mul_of_pos_right hgeom' hL
  have hscale0 : D.scale x 0 = D.s' * L x := by simp [BandData.scale]
  calc
    _ ≤ D.c₂ * ((D.r₀ : ℝ) * D.scale x j) :=
      mul_le_mul_of_nonneg_left
        (tail_slot_scale_sum_le D hD x hL j hratio) hc₂.le
    _ = ((D.r₀ : ℝ) * D.c₂ * D.s' / 2 ^ j) * L x := by
      simp [BandData.scale, hratio]
      ring
    _ < ((D.c₂ - D.c₁) * D.s' / 24) * L x := hgeomL
    _ = (D.c₂ - D.c₁) / 24 * D.scale x 0 := by
      rw [hscale0]
      ring

lemma terminal_midpoint_remainder_small (D : BandData) (hD : D.Valid) :
    ∀ᶠ x : ℝ in atTop,
      (D.r₀ : ℝ) * ((D.c₁ + D.c₂) / 2) * D.scale x (D.last x) ≤
        (D.c₂ - D.c₁) * D.s' / 16 * L x := by
  obtain ⟨hr₀N, hc₁, hc₁₂, hs', _, _, _, _, cmin, cmax,
    _, hcmax, hdata⟩ := hD
  have hr₀ : (0 : ℝ) < (D.r₀ : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp hr₀N)
  have hc₂ : 0 < D.c₂ := hc₁.trans hc₁₂
  have hm : 0 < (D.c₁ + D.c₂) / 2 := by positivity
  have hbudget : 0 < (D.c₂ - D.c₁) * D.s' / 8 := by
    exact div_pos (mul_pos (sub_pos.mpr hc₁₂) hs') (by norm_num)
  let K : ℝ := (D.r₀ : ℝ) * ((D.c₁ + D.c₂) / 2) * cmax
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsmall := Erdos821.S56Core.loglog_le_small_log
    ((D.c₂ - D.c₁) * D.s' / 8) K hbudget hK
  filter_upwards [hdata, hsmall] with x hx hsmallx
  have hlast : D.scale x (D.last x) ≤ cmax * T x := hx.2.2.1
  have hcoeff : 0 ≤ (D.r₀ : ℝ) * ((D.c₁ + D.c₂) / 2) := by positivity
  calc
    _ ≤ ((D.r₀ : ℝ) * ((D.c₁ + D.c₂) / 2)) * (cmax * T x) :=
      mul_le_mul_of_nonneg_left hlast hcoeff
    _ = K * T x := by dsimp [K]; ring
    _ ≤ (D.c₂ - D.c₁) * D.s' / 16 * L x := by
      calc
        _ ≤ (((D.c₂ - D.c₁) * D.s' / 8) / 2) * L x := hsmallx
        _ = _ := by ring

lemma outside_log_deviation_bound (D : BandData) (hD : D.Valid)
    {x : ℝ} {jstar : ℕ} (hL : 0 < L x) (hratio : D.ratio = 2)
    (P : ℕ) (z : D.Lists x jstar) (s : D.Slot x) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hgeom : 2 * (D.r₀ : ℝ) * D.c₂ * D.s' / 2 ^ (P + 1) <
      (D.c₂ - D.c₁) * D.s' / 24)
    (hprefix : ∀ t : D.Slot x, t ≠ s → t.1.val ≤ P →
      |Real.log (z t).val - (D.c₁ + D.c₂) / 2 * D.scale x t.1.val| ≤
        epsilon * D.scale x t.1.val) :
    |(Finset.univ.erase s).sum (fun t : D.Slot x =>
        Real.log (z t).val - (D.c₁ + D.c₂) / 2 * D.scale x t.1.val)| ≤
      2 * (D.r₀ : ℝ) * epsilon * D.scale x 0 +
        (D.c₂ - D.c₁) / 24 * D.scale x 0 := by
  let m : ℝ := (D.c₁ + D.c₂) / 2
  let U : Finset (D.Slot x) := Finset.univ.erase s
  let V : Finset (D.Slot x) := U.filter (fun t => P < t.1.val)
  let err : D.Slot x → ℝ := fun t =>
    Real.log (z t).val - m * D.scale x t.1.val
  have hc₁ : 0 < D.c₁ := hD.2.1
  have hc₁₂ : D.c₁ < D.c₂ := hD.2.2.1
  have hc₂ : 0 < D.c₂ := hc₁.trans hD.2.2.1
  have hpoint : ∀ t ∈ U,
      |err t| ≤ epsilon * D.scale x t.1.val +
        if P < t.1.val then D.c₂ * D.scale x t.1.val else 0 := by
    intro t ht
    have hne : t ≠ s := by simpa [U] using ht
    by_cases htail : P < t.1.val
    · have hscl := Erdos821.S56Core.scale_pos D hD x hL t.1.val
      have hlogs := Erdos821.S56Core.slot_log_bounds D z t
      have hmidle : m * D.scale x t.1.val ≤ D.c₂ * D.scale x t.1.val := by
        dsimp [m]
        apply mul_le_mul_of_nonneg_right _ hscl.le
        linarith
      have hlognonneg : 0 ≤ Real.log (z t).val :=
        (mul_nonneg hc₁.le hscl.le).trans hlogs.1
      have hmidnonneg : 0 ≤ m * D.scale x t.1.val := by
        dsimp [m]
        positivity
      have habs : |Real.log (z t).val - m * D.scale x t.1.val| ≤
          D.c₂ * D.scale x t.1.val := by
        rw [abs_le]
        constructor <;> nlinarith [hlogs.2, hmidle, hlognonneg, hmidnonneg]
      change |Real.log (z t).val - m * D.scale x t.1.val| ≤ _
      simp [htail]
      nlinarith [habs, mul_nonneg hc₂.le hscl.le]
    · have hband : t.1.val ≤ P := Nat.le_of_not_gt htail
      have he := hprefix t hne hband
      change |Real.log (z t).val - m * D.scale x t.1.val| ≤ _
      simpa [m, htail] using he
  have hsumPoint :
      (∑ t ∈ U, |err t|) ≤
        epsilon * (∑ t ∈ U, D.scale x t.1.val) +
          D.c₂ * (∑ t ∈ V, D.scale x t.1.val) := by
    have hfactorPrefix :
        (∑ t ∈ U, epsilon * D.scale x t.1.val) =
          epsilon * (∑ t ∈ U, D.scale x t.1.val) := by
      rw [← Finset.mul_sum]
    have hfactorTail :
        (∑ t ∈ U, if P < t.1.val then D.c₂ * D.scale x t.1.val else 0) =
          D.c₂ * (∑ t ∈ V, D.scale x t.1.val) := by
      rw [← Finset.sum_filter, Finset.mul_sum]
    calc
      _ ≤ ∑ t ∈ U,
          (epsilon * D.scale x t.1.val +
            if P < t.1.val then D.c₂ * D.scale x t.1.val else 0) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hpoint t ht
      _ = (∑ t ∈ U, epsilon * D.scale x t.1.val) +
          (∑ t ∈ U, if P < t.1.val then D.c₂ * D.scale x t.1.val else 0) := by
        rw [Finset.sum_add_distrib]
      _ = _ := by rw [hfactorPrefix, hfactorTail]
  have hUsubset : U ⊆ Finset.univ := by simp [U]
  have hUscale : (∑ t ∈ U, D.scale x t.1.val) ≤
      2 * (D.r₀ : ℝ) * D.scale x 0 := by
    calc
      _ ≤ ∑ t : D.Slot x, D.scale x t.1.val :=
        Finset.sum_le_sum_of_subset_of_nonneg hUsubset
          (fun t _ _ => (Erdos821.S56Core.scale_pos D hD x hL t.1.val).le)
      _ ≤ 2 * (D.r₀ : ℝ) * D.scale x 0 :=
        all_slot_scale_sum_le D hD x hL hratio
  have hVsubset : V ⊆ Finset.univ.filter (fun t : D.Slot x => P < t.1.val) := by
    intro t ht
    have ht' : t ∈ U ∧ P < t.1.val := by simpa [V] using ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'.2⟩
  have hVscale : (∑ t ∈ V, D.scale x t.1.val) ≤
      ∑ t ∈ Finset.univ.filter (fun t : D.Slot x => P < t.1.val),
        D.scale x t.1.val :=
    Finset.sum_le_sum_of_subset_of_nonneg hVsubset
      (fun t _ _ => (Erdos821.S56Core.scale_pos D hD x hL t.1.val).le)
  have htail := tail_deviation_budget D hD x hL P hratio hgeom
  have htailV : D.c₂ * (∑ t ∈ V, D.scale x t.1.val) ≤
      (D.c₂ - D.c₁) / 24 * D.scale x 0 :=
    (mul_le_mul_of_nonneg_left hVscale hc₂.le).trans htail.le
  calc
    _ ≤ epsilon * (∑ t ∈ U, D.scale x t.1.val) +
        D.c₂ * (∑ t ∈ V, D.scale x t.1.val) := by
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) hsumPoint
    _ ≤ 2 * (D.r₀ : ℝ) * epsilon * D.scale x 0 +
        (D.c₂ - D.c₁) / 24 * D.scale x 0 := by
      have heps := mul_le_mul_of_nonneg_left hUscale hepsilon
      nlinarith

lemma log_outside_slot_product (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (s : D.Slot x) :
    Real.log (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) =
      (Finset.univ.erase s).sum (fun t : D.Slot x => Real.log (z t).val) := by
  simp only [Erdos821.P7Core.outsideSlotProduct, Nat.cast_prod]
  apply Real.log_prod
  intro t ht
  have hp : (0 : ℝ) < (z t).val := by
    exact_mod_cast Erdos821.S56Core.slot_value_pos D z t
  exact hp.ne'

theorem CandidatePlacementTask_proof :
    Erdos821.P7Core.CandidatePlacementTask := by
  intro δ C hC
  let D : BandData := C.bands
  let gap : ℝ := D.c₂ - D.c₁
  let epsilon : ℝ := gap / (64 * (D.r₀ : ℝ))
  let sigma : ℝ := gap * D.s' / 64
  rcases hC with ⟨hDorig, _, _, hratio, hsprime, _, _, _, hgeom, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hD : D.Valid := by simpa [D] using hDorig
  have hratioD : D.ratio = 2 := by simpa [D] using hratio
  have hsprimeD : D.s' = 1 / ((D.r₀ : ℝ) * (D.c₁ + D.c₂)) := by
    simpa [D] using hsprime
  have hgeomD : 2 * (D.r₀ : ℝ) * D.c₂ * D.s' / 2 ^ (C.prefixLen + 1) <
      (D.c₂ - D.c₁) * D.s' / 24 := by
    simpa [D] using hgeom
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hD.2.2.1
  have hs' : 0 < D.s' := hD.2.2.2.1
  have hr₀ : 0 < (D.r₀ : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp hD.1)
  have hr₀ge : (1 : ℝ) ≤ (D.r₀ : ℝ) := by exact_mod_cast hD.1
  have hden : 4 < 64 * (D.r₀ : ℝ) := by nlinarith
  have hepsilonPos : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos hgap (by positivity)
  have hepsilonLt : epsilon < gap / 4 := by
    dsimp [epsilon]
    exact (div_lt_div_iff₀ (by positivity) (by norm_num)).2
      (mul_lt_mul_of_pos_left hden hgap)
  have hsigmaPos : 0 < sigma := by
    dsimp [sigma]
    exact div_pos (mul_pos hgap hs') (by norm_num)
  have hlog2event : ∀ᶠ x : ℝ in atTop,
      Real.log 2 ≤ gap * D.s' / 8 * L x := by
    have hlarge := Erdos821.S56Core.tendsto_L.eventually_ge_atTop
      (8 * Real.log 2 / (gap * D.s'))
    filter_upwards [hlarge] with x hx
    have hscale : (gap * D.s' / 8) * (8 * Real.log 2 / (gap * D.s')) =
        Real.log 2 := by
      have hnz : gap * D.s' ≠ 0 := (mul_pos hgap hs').ne'
      field_simp [hnz]
    calc
      _ = (gap * D.s' / 8) * (8 * Real.log 2 / (gap * D.s')) := hscale.symm
      _ ≤ (gap * D.s' / 8) * L x :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ = gap * D.s' / 8 * L x := by ring
  have hterminal := terminal_midpoint_remainder_small D hD
  refine ⟨epsilon, sigma, hepsilonPos, ?_, hsigmaPos, ?_⟩
  · simpa [gap, D] using hepsilonLt
  · intro a b ha hab hb jstar hj
    filter_upwards [hterminal, hlog2event, Filter.eventually_gt_atTop (1 : ℝ)]
      with x hterminalx hlog2x hxlarge
    intro s hsSlot0 hsSlotK z hEvent r hr hrx
    have hxpos : 0 < x := by linarith
    have hL : 0 < L x := by
      change 0 < Real.log x
      exact Real.log_pos hxlarge
    let m : ℝ := (D.c₁ + D.c₂) / 2
    let S₀ : ℝ := D.scale x 0
    let miss : ℝ := (D.r₀ : ℝ) * m * D.scale x (D.last x)
    let B : ℝ := gap * S₀ / 32 + gap / 24 * S₀
    let U : Finset (D.Slot x) := Finset.univ.erase s
    let E : ℝ := U.sum (fun t : D.Slot x =>
      Real.log (z t).val - m * D.scale x t.1.val)
    have hS₀ : S₀ = D.s' * L x := by
      simp [S₀, BandData.scale]
    have hS₀pos : 0 < S₀ := by
      simpa [S₀] using Erdos821.S56Core.scale_pos D hD x hL 0
    have hmiss : miss ≤ gap * S₀ / 16 := by
      calc
        _ ≤ gap * D.s' / 16 * L x := by
          simpa [miss, m, gap] using hterminalx
        _ = gap * S₀ / 16 := by rw [hS₀]; ring
    have hmissNonneg : 0 ≤ miss := by
      have hc₁ : 0 < D.c₁ := hD.2.1
      have hc₂ : 0 < D.c₂ := hc₁.trans hD.2.2.1
      have hmpos : 0 < m := by dsimp [m]; positivity
      have hlastpos := Erdos821.S56Core.scale_pos D hD x hL (D.last x)
      change 0 ≤ (D.r₀ : ℝ) * m * D.scale x (D.last x)
      exact mul_nonneg (mul_nonneg hr₀.le hmpos.le) hlastpos.le
    have hdev₀ := outside_log_deviation_bound D hD hL hratioD C.prefixLen z s
      epsilon hepsilonPos.le hgeomD (by
        intro t ht hband
        exact hEvent t ht hband)
    have hepsilonErr : 2 * (D.r₀ : ℝ) * epsilon * S₀ = gap * S₀ / 32 := by
      dsimp [epsilon]
      field_simp [hr₀.ne']; ring
    have hdev : |E| ≤ B := by
      calc
        _ ≤ 2 * (D.r₀ : ℝ) * epsilon * S₀ + gap / 24 * S₀ := by
          simpa only [E, U, m, S₀] using hdev₀
        _ = B := by
          dsimp [B]
          rw [hepsilonErr]
    have hcenterFull := full_midpoint_sum D hD x hratioD hsprimeD
    have hcenterTotal :
        (∑ t : D.Slot x, m * D.scale x t.1.val) = L x - miss := by
      simpa [m, miss] using hcenterFull
    have hErase :
        (∑ t ∈ U, m * D.scale x t.1.val) + m * S₀ =
          ∑ t : D.Slot x, m * D.scale x t.1.val := by
      have h := Finset.sum_erase_add (Finset.univ : Finset (D.Slot x))
        (fun t => m * D.scale x t.1.val) (Finset.mem_univ s)
      have h' :
          (∑ t ∈ U, m * D.scale x t.1.val) +
              m * D.scale x s.1.val =
            ∑ t : D.Slot x, m * D.scale x t.1.val := by
        simp [U]
      simpa [hsSlot0] using h'
    have hcenterErase :
        (∑ t ∈ U, m * D.scale x t.1.val) = L x - miss - m * S₀ := by
      rw [hcenterTotal] at hErase
      linarith
    have hlogSum :
        (∑ t ∈ U, Real.log (z t).val) =
          (∑ t ∈ U, m * D.scale x t.1.val) + E := by
      dsimp [E]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp [m]
      ring
    have hlogProduct :
        Real.log (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) =
          L x - miss - m * S₀ + E := by
      calc
        _ = (Finset.univ.erase s).sum (fun t : D.Slot x => Real.log (z t).val) :=
          log_outside_slot_product D z s
        _ = ∑ t ∈ U, Real.log (z t).val := by rfl
        _ = L x - miss - m * S₀ + E := by rw [hlogSum, hcenterErase]
    have hEupper : E ≤ B := (abs_le.mp hdev).2
    have hElower : -B ≤ E := (abs_le.mp hdev).1
    have hlow : m * S₀ - B ≤
        L x - Real.log (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) := by
      rw [hlogProduct]
      linarith [hmissNonneg, hEupper]
    have hhigh :
        L x - Real.log (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) ≤
          m * S₀ + miss + B := by
      rw [hlogProduct]
      linarith [hElower]
    have hprodNat : 0 < Erdos821.P7Core.outsideSlotProduct D z s := by
      unfold Erdos821.P7Core.outsideSlotProduct
      apply Finset.prod_pos
      intro t ht
      exact Erdos821.S56Core.slot_value_pos D z t
    have hprodpos :
        0 < (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) := by
      exact_mod_cast hprodNat
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
    have hrone : (1 : ℝ) ≤ (r : ℝ) := by
      have hn : 1 ≤ r := by omega
      exact_mod_cast hn
    have hlogrNonneg : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrone
    have hlogpow : Real.log (x ^ sigma) = sigma * L x := by
      rw [Real.log_rpow hxpos]
      rfl
    have hlogr : Real.log (r : ℝ) ≤ sigma * L x := by
      calc
        _ ≤ Real.log (x ^ sigma) := Real.log_le_log hrpos hrx
        _ = sigma * L x := hlogpow
    have hbpos : 0 < b := lt_trans zero_lt_one (ha.trans hab)
    have hlogbNonneg : 0 ≤ Real.log b := Real.log_nonneg (le_of_lt (ha.trans hab))
    have hlog2S₀ : Real.log 2 ≤ gap * S₀ / 8 := by
      calc
        _ ≤ gap * D.s' / 8 * L x := hlog2x
        _ = gap * S₀ / 8 := by rw [hS₀]; ring
    have hlogb : Real.log b ≤ gap * S₀ / 8 :=
      (Real.log_le_log hbpos hb.le).trans hlog2S₀
    have hsigL : sigma * L x = gap * S₀ / 64 := by
      rw [hS₀]
      dsimp [sigma, gap]
      ring
    have hcostCoefficient :
        (1 : ℝ) / 16 + 1 / 8 + 1 / 32 + 1 / 24 + 1 / 64 < 1 / 2 := by
      norm_num
    have hcostScale :
        gap * S₀ / 16 + gap * S₀ / 8 + gap * S₀ / 32 +
          gap * S₀ / 24 + gap * S₀ / 64 < gap * S₀ / 2 := by
      calc
        _ = gap * S₀ *
            ((1 : ℝ) / 16 + 1 / 8 + 1 / 32 + 1 / 24 + 1 / 64) := by ring
        _ < gap * S₀ * (1 / 2) :=
          mul_lt_mul_of_pos_left hcostCoefficient (mul_pos hgap hS₀pos)
        _ = gap * S₀ / 2 := by ring
    have hmissLog : miss + Real.log b ≤ gap * S₀ / 16 + gap * S₀ / 8 :=
      add_le_add hmiss hlogb
    have hmargin : miss + B + sigma * L x + Real.log b < gap / 2 * S₀ := by
      rw [hsigL]
      dsimp [B]
      calc
        _ = (miss + Real.log b) + gap * S₀ / 32 +
            gap * S₀ / 24 + gap * S₀ / 64 := by ring
        _ ≤ gap * S₀ / 16 + gap * S₀ / 8 + gap * S₀ / 32 +
            gap * S₀ / 24 + gap * S₀ / 64 := by
          calc
            _ = (miss + Real.log b) +
                (gap * S₀ / 32 + gap * S₀ / 24 + gap * S₀ / 64) := by ring
            _ ≤ (gap * S₀ / 16 + gap * S₀ / 8) +
                (gap * S₀ / 32 + gap * S₀ / 24 + gap * S₀ / 64) :=
              add_le_add_left hmissLog _
            _ = _ := by ring
        _ < gap * S₀ / 2 := hcostScale
        _ = gap / 2 * S₀ := by ring
    have hlowmargin : B + sigma * L x < gap / 2 * S₀ := by
      have hnonneg : 0 ≤ miss + Real.log b := add_nonneg hmissNonneg hlogbNonneg
      have hle : B + sigma * L x ≤ miss + B + sigma * L x + Real.log b := by
        have h := add_le_add_left hnonneg (B + sigma * L x)
        simpa [add_assoc, add_comm, add_left_comm] using h
      exact hle.trans_lt hmargin
    have hhighmargin : miss + B + Real.log b ≤ gap / 2 * S₀ := by
      have hsigNonneg : 0 ≤ sigma * L x := mul_nonneg hsigmaPos.le hL.le
      have hle : miss + B + Real.log b ≤
          miss + B + Real.log b + sigma * L x := by
        have h := add_le_add_left hsigNonneg (miss + B + Real.log b)
        simpa [add_assoc, add_comm, add_left_comm] using h
      have hmarginLe : miss + B + Real.log b + sigma * L x ≤ gap / 2 * S₀ := by
        simpa [add_assoc, add_comm, add_left_comm] using hmargin.le
      exact hle.trans hmarginLe
    have hmidlow : m * S₀ - D.c₁ * S₀ = gap / 2 * S₀ := by
      dsimp [m, gap]
      ring
    have hmidhigh : D.c₂ * S₀ - m * S₀ = gap / 2 * S₀ := by
      dsimp [m, gap]
      ring
    have hlogRatio (c : ℝ) (hc : 0 < c) :
        Real.log (c * x / ((r : ℝ) *
          (Erdos821.P7Core.outsideSlotProduct D z s : ℝ))) =
          Real.log c + L x - Real.log (r : ℝ) -
            Real.log (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) := by
      have hnum : 0 < c * x := mul_pos hc hxpos
      have hden : 0 < (r : ℝ) *
          (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) := mul_pos hrpos hprodpos
      rw [Real.log_div hnum.ne' hden.ne']
      rw [Real.log_mul hc.ne' hxpos.ne', Real.log_mul hrpos.ne' hprodpos.ne']
      simp only [L]
      ring
    have hlogA :
        Real.log (a * x / ((r : ℝ) *
          (Erdos821.P7Core.outsideSlotProduct D z s : ℝ))) =
          Real.log a + L x - Real.log (r : ℝ) -
            Real.log (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) :=
      hlogRatio a (lt_trans zero_lt_one ha)
    have hlogB :
        Real.log (b * x / ((r : ℝ) *
          (Erdos821.P7Core.outsideSlotProduct D z s : ℝ))) =
          Real.log b + L x - Real.log (r : ℝ) -
            Real.log (Erdos821.P7Core.outsideSlotProduct D z s : ℝ) :=
      hlogRatio b hbpos
    have hlogLower : D.c₁ * S₀ ≤
        Real.log (a * x / ((r : ℝ) *
          (Erdos821.P7Core.outsideSlotProduct D z s : ℝ))) := by
      rw [hlogA]
      have haLog : 0 ≤ Real.log a := Real.log_nonneg (le_of_lt ha)
      have hroom : D.c₁ * S₀ ≤ m * S₀ - B - sigma * L x := by
        linarith only [hlowmargin, hmidlow]
      linarith only [hlow, hlogr, haLog, hroom]
    have hlogUpper :
        Real.log (b * x / ((r : ℝ) *
          (Erdos821.P7Core.outsideSlotProduct D z s : ℝ))) ≤ D.c₂ * S₀ := by
      rw [hlogB]
      have hle : Real.log b + (m * S₀ + miss + B) ≤ D.c₂ * S₀ := by
        linarith only [hhighmargin, hmidhigh]
      linarith only [hhigh, hlogrNonneg, hle]
    have hratioAPos : 0 < a * x / ((r : ℝ) *
        (Erdos821.P7Core.outsideSlotProduct D z s : ℝ)) :=
      div_pos (mul_pos (lt_trans zero_lt_one ha) hxpos) (mul_pos hrpos hprodpos)
    have hratioBPos : 0 < b * x / ((r : ℝ) *
        (Erdos821.P7Core.outsideSlotProduct D z s : ℝ)) :=
      div_pos (mul_pos hbpos hxpos) (mul_pos hrpos hprodpos)
    have hleft : Real.exp (D.c₁ * S₀) ≤
        a * x / ((r : ℝ) * Erdos821.P7Core.outsideSlotProduct D z s) := by
      calc
        _ ≤ Real.exp (Real.log (a * x / ((r : ℝ) *
            (Erdos821.P7Core.outsideSlotProduct D z s : ℝ)))) :=
          Real.exp_le_exp.mpr hlogLower
        _ = _ := Real.exp_log hratioAPos
    have hright :
        b * x / ((r : ℝ) * Erdos821.P7Core.outsideSlotProduct D z s) ≤
          Real.exp (D.c₂ * S₀) := by
      calc
        _ = Real.exp (Real.log (b * x / ((r : ℝ) *
            (Erdos821.P7Core.outsideSlotProduct D z s : ℝ)))) :=
          (Real.exp_log hratioBPos).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlogUpper
    exact ⟨hleft, hright⟩

end Erdos821.P7Place

