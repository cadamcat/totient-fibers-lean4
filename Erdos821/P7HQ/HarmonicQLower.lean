import Erdos821.P7.HarmonicQLowerTask
import Erdos821.P7Band.Proof
import Erdos821.S56.BandSize
import Erdos821.S56.GeometricScales
import PrimeNumberTheoremAnd.Erdos970.MertensClassical

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Hq
open Erdos821.Blueprint Erdos821.Blueprint.Analytic
open Erdos970.Mertens

/-- A fixed logarithmic interval has positive reciprocal prime mass, by the
sharp Mertens error. The interval uses open lower endpoints of floors so it
embeds in the literal ceiling/floor band without an endpoint convention. -/
theorem interval_reciprocal_mass_lower (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ Y : ℝ, ∀ y : ℝ, 0 < y → Y ≤ Real.exp (a * y) →
      Real.log (b / a) / 2 ≤
        ∑ p ∈ Finset.Ioc ⌊Real.exp (a * y)⌋₊ ⌊Real.exp (b * y)⌋₊ with p.Prime,
          (1 : ℝ) / p := by
  have hb : 0 < b := lt_trans ha hab
  have hratio : 1 < b / a := (one_lt_div ha).2 hab
  have hlog : 0 < Real.log (b / a) := Real.log_pos hratio
  have hE : Tendsto E₂p atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp E₂p.bound'
  have hev : ∀ᶠ z in atTop, |E₂p z| < Real.log (b / a) / 4 := by
    have h := (Metric.tendsto_nhds.mp hE) (Real.log (b / a) / 4) (by positivity)
    simpa [Real.dist_eq] using h
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hev
  refine ⟨Y, fun y hy hYlo => ?_⟩
  let lo : ℝ := Real.exp (a * y)
  let hi : ℝ := Real.exp (b * y)
  have hlo_pos : 0 < lo := Real.exp_pos _
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hfloor : ⌊lo⌋₊ ≤ ⌊hi⌋₊ := Nat.floor_le_floor hlohi
  have hsplit :
      (∑ p ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊ with p.Prime, (1 : ℝ) / p) =
        (∑ p ∈ Finset.Ioc 0 ⌊hi⌋₊ with p.Prime, (1 : ℝ) / p) -
          ∑ p ∈ Finset.Ioc 0 ⌊lo⌋₊ with p.Prime, (1 : ℝ) / p := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfloor]
    ring
  have hlogs : Real.log (Real.log hi) - Real.log (Real.log lo) = Real.log (b / a) := by
    dsimp [hi, lo]
    rw [Real.log_exp, Real.log_exp]
    rw [← Real.log_div (mul_ne_zero hb.ne' hy.ne') (mul_ne_zero ha.ne' hy.ne')]
    congr 1
    field_simp
  have helo := hY lo (by simpa [lo] using hYlo)
  have hehi := hY hi (hYlo.trans (by simpa [lo, hi] using hlohi))
  rw [abs_lt] at helo hehi
  rw [hsplit, sum_prime_div_eq, sum_prime_div_eq]
  have hcancel :
      (Real.log (Real.log hi) + M + E₂p hi) -
        (Real.log (Real.log lo) + M + E₂p lo) =
          Real.log (b / a) + E₂p hi - E₂p lo := by
    rw [← hlogs]
    ring
  rw [hcancel]
  nlinarith [helo.1, helo.2, hehi.1, hehi.2]

/-- When a band is at least 6/5 wide, the dyadic group from P7Band embeds
inside the literal prime band. -/
theorem canonical_grp_subset_band (D : BandData) (x : ℝ) (j : ℕ)
    (hc₁ : 0 < D.c₁) (hc₂ : 0 < D.c₂) (hscale : 0 < D.scale x j)
    (hwide : (6 / 5 : ℝ) ≤ D.c₂ / D.c₁) :
    P7Band.grp ((2 / 3 : ℝ) * D.c₁ * D.scale x j) ⊆ D.band x j := by
  let b : ℝ := (2 / 3 : ℝ) * D.c₁ * D.scale x j
  have hb : 0 < b := by dsimp [b]; positivity
  have hlo : (3 / 2 : ℝ) * b = D.c₁ * D.scale x j := by
    dsimp [b]
    ring
  have hlo' : (3 / 2 : ℝ) * ((2 / 3 : ℝ) * D.c₁ * D.scale x j) =
      D.c₁ * D.scale x j := by ring
  have hhi : (9 / 5 : ℝ) * b ≤ D.c₂ * D.scale x j := by
    calc
      (9 / 5 : ℝ) * b = (6 / 5 : ℝ) * (D.c₁ * D.scale x j) := by
        dsimp [b]
        ring
      _ ≤ (D.c₂ / D.c₁) * (D.c₁ * D.scale x j) :=
        mul_le_mul_of_nonneg_right hwide (mul_nonneg hc₁.le hscale.le)
      _ = D.c₂ * D.scale x j := by field_simp [hc₁.ne']
  intro p hp
  obtain ⟨hpprime, hplower, hpupper⟩ := P7Band.mem_grp.mp hp
  have hpLower : Real.exp (D.c₁ * D.scale x j) < (p : ℝ) := by
    simpa only [hlo'] using hplower
  have hpceil : ⌈Real.exp (D.c₁ * D.scale x j)⌉₊ ≤ p := Nat.ceil_le.mpr hpLower.le
  have hpupper' : (p : ℝ) ≤ Real.exp (D.c₂ * D.scale x j) := by
    exact hpupper.trans (Real.exp_le_exp.mpr hhi)
  have hpfloor : p ≤ ⌊Real.exp (D.c₂ * D.scale x j)⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos _).le).2 hpupper'
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpceil, hpfloor⟩, hpprime⟩

/-- Every pure band has a common positive reciprocal mass once the terminal
scale tends to infinity. The constant depends only on the fixed band data. -/
theorem eventually_pure_band_mass_lower (D : BandData) (hD : D.Valid) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 / 2 ∧ ∀ᶠ x : ℝ in atTop,
      ∀ j ≤ D.last x, k ≤ ∑ p ∈ D.band x j, (1 : ℝ) / p := by
  have hvalid := hD
  obtain ⟨hr₀, hc₁, hc₁₂, hs', hratio, hsmall, hroom, hlast,
    cmin, cmax, hcmin, hcmax, hevent⟩ := hD
  have hc₂ : 0 < D.c₂ := hc₁.trans hc₁₂
  have ⟨Y, hY⟩ := interval_reciprocal_mass_lower D.c₁ D.c₂ hc₁ hc₁₂
  obtain ⟨Yg, hG⟩ := P7Band.grp_mass_eventually
  let k : ℝ := min (min (Real.log (D.c₂ / D.c₁) / 2)
    (Real.log (6 / 5) / 2)) (1 / 2)
  have hratio' : 1 < D.c₂ / D.c₁ := (one_lt_div hc₁).2 hc₁₂
  have hklog : 0 < Real.log (D.c₂ / D.c₁) / 2 := by
    apply div_pos (Real.log_pos hratio')
    norm_num
  have hkdyad : 0 < Real.log (6 / 5) / 2 := by
    apply div_pos (Real.log_pos (by norm_num))
    norm_num
  have hk : 0 < k := by
    dsimp [k]
    exact lt_min (lt_min hklog hkdyad) (by norm_num)
  have hkhalf : k ≤ 1 / 2 := by dsimp [k]; exact min_le_right _ _
  have hkinterval : k ≤ Real.log (D.c₂ / D.c₁) / 2 := by
    dsimp [k]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hkgroup : k ≤ Real.log (6 / 5) / 2 := by
    dsimp [k]
    exact (min_le_left _ _).trans (min_le_right _ _)
  let Y₁ : ℝ := max 1 (max Y Yg)
  let A : ℝ := max 1 (Real.log Y₁ / (D.c₁ * cmin))
  have hA : 0 ≤ A := le_trans (by norm_num) (le_max_left _ _)
  have hlargeT : ∀ᶠ x : ℝ in atTop, A ≤ T x :=
    Erdos821.S56Core.tendsto_T.eventually (eventually_ge_atTop A)
  have hlargeL : ∀ᶠ x : ℝ in atTop, 0 < L x :=
    Erdos821.S56Core.tendsto_L.eventually (eventually_gt_atTop 0)
  refine ⟨k, hk, hkhalf, ?_⟩
  filter_upwards [hevent, hlargeT, hlargeL] with x hx hT hL
  intro j hj
  have hscale : cmin * T x ≤ D.scale x j := by
    exact hx.2.1.trans (Erdos821.S56Core.scale_antitone D hvalid x hL j (D.last x) hj)
  have hlogY : Real.log Y₁ ≤ D.c₁ * D.scale x j := by
    have hT' : Real.log Y₁ / (D.c₁ * cmin) ≤ T x :=
      (le_max_right _ _).trans hT
    have hY' : Real.log Y₁ ≤ (D.c₁ * cmin) * T x := by
      calc
        Real.log Y₁ ≤ T x * (D.c₁ * cmin) :=
          (div_le_iff₀ (mul_pos hc₁ hcmin)).mp hT'
        _ = (D.c₁ * cmin) * T x := by ring
    have hsc := mul_le_mul_of_nonneg_left hscale hc₁.le
    nlinarith
  have hY₁le : Y₁ ≤ Real.exp (D.c₁ * D.scale x j) := by
    have hypos : 0 < Y₁ := by dsimp [Y₁]; positivity
    have h := Real.exp_le_exp.mpr hlogY
    rw [Real.exp_log hypos] at h
    exact h
  have hYexp : Y ≤ Real.exp (D.c₁ * D.scale x j) :=
    (le_max_left Y Yg).trans ((le_max_right 1 (max Y Yg)).trans hY₁le)
  have hYgexp : Yg ≤ Real.exp (D.c₁ * D.scale x j) :=
    (le_max_right Y Yg).trans ((le_max_right 1 (max Y Yg)).trans hY₁le)
  have hscalePos : 0 < D.scale x j :=
    Erdos821.S56Core.scale_pos D hvalid x hL j
  let lo : ℝ := Real.exp (D.c₁ * D.scale x j)
  let hi : ℝ := Real.exp (D.c₂ * D.scale x j)
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsubset :
      (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime ⊆ D.band x j := by
    intro p hp
    obtain ⟨hpI, hpprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpl, hpu⟩ := Finset.mem_Ioc.mp hpI
    have hpabove : lo ≤ (p : ℝ) := by
      have hnextNat : ⌊lo⌋₊ + 1 ≤ p := by omega
      have hnext : (⌊lo⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hnextNat
      exact (Nat.lt_floor_add_one lo).le.trans hnext
    have hpceil : ⌈lo⌉₊ ≤ p := Nat.ceil_le.mpr hpabove
    change p ∈ (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x j)⌉₊
      ⌊Real.exp (D.c₂ * D.scale x j)⌋₊).filter Nat.Prime
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by simpa [lo] using hpceil,
      by simpa [hi] using hpu⟩, hpprime⟩
  have hinterval := hY (D.scale x j) hscalePos hYexp
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun p _ _ => show 0 ≤ (1 : ℝ) / (p : ℝ) by positivity)
  have hband := hinterval.trans hmass
  by_cases hwide : (6 / 5 : ℝ) ≤ D.c₂ / D.c₁
  · let b : ℝ := (2 / 3 : ℝ) * D.c₁ * D.scale x j
    have hb : 0 < b := by dsimp [b]; positivity
    have harg : (3 / 2 : ℝ) * b = D.c₁ * D.scale x j := by
      dsimp [b]
      ring
    have hgroup := hG b hb (by rw [harg]; exact hYgexp)
    have hsubgroup := canonical_grp_subset_band D x j hc₁ hc₂ hscalePos hwide
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubgroup
      (fun p _ _ => show 0 ≤ (1 : ℝ) / (p : ℝ) by positivity)
    exact hkgroup.trans (hgroup.1.trans hsum)
  · exact hkinterval.trans hband

/-- The square root of a logarithm is eventually below any fixed positive
multiple of that logarithm. -/
theorem eventually_sqrt_log_lt_linear (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt (L x) < a * L x := by
  have hlarge : ∀ᶠ x : ℝ in atTop,
      max 1 ((2 / a + 2) ^ 2) ≤ L x :=
    Erdos821.S56Core.tendsto_L.eventually
      (eventually_ge_atTop (max 1 ((2 / a + 2) ^ 2)))
  filter_upwards [hlarge] with x hL
  have hL1 : 1 ≤ L x := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ L x := by linarith
  have hcoef : 0 ≤ 2 / a + 2 := by positivity
  have hsqrt : 2 / a + 2 ≤ Real.sqrt (L x) :=
    (Real.le_sqrt hcoef hL0).mpr ((le_max_right _ _).trans hL)
  have hdiv : 2 / a ≤ Real.sqrt (L x) := by linarith
  have hmul : 2 ≤ Real.sqrt (L x) * a := (div_le_iff₀ ha).mp hdiv
  have hmain : 2 * Real.sqrt (L x) ≤ a * L x := by
    calc
      2 * Real.sqrt (L x) ≤ (Real.sqrt (L x) * a) * Real.sqrt (L x) :=
        mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg _)
      _ = a * (Real.sqrt (L x) * Real.sqrt (L x)) := by ring
      _ = a * L x := by rw [Real.mul_self_sqrt hL0]
  have hsqrtpos : 0 < Real.sqrt (L x) := Real.sqrt_pos.mpr (by linarith)
  exact lt_of_lt_of_le (by linarith) hmain

/-- For a fixed slot index, all primes in its band eventually exceed the
roughness threshold, so they remain available in the exceptional slot. -/
theorem eventually_band_primes_rough (D : BandData) (hD : D.Valid)
    (jstar : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ D.band x jstar, rough (W x) p := by
  obtain ⟨_, hc₁, hc₁₂, hs', hratio, _, _, _, _, _, _, _, _⟩ := hD
  let a : ℝ := D.c₁ * D.s' / D.ratio ^ jstar
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos hc₁ hs') (pow_pos (lt_trans zero_lt_one hratio) _)
  have hW : ∀ᶠ x : ℝ in atTop, W x < Real.exp (a * L x) := by
    filter_upwards [eventually_sqrt_log_lt_linear a ha] with x hx
    change Real.exp (Real.sqrt (L x)) < Real.exp (a * L x)
    exact Real.exp_lt_exp.mpr hx
  filter_upwards [hW] with x hxW
  intro p hp
  obtain ⟨hpI, hpprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hplo, _⟩ := Finset.mem_Icc.mp hpI
  have harg : a * L x = D.c₁ * D.scale x jstar := by
    dsimp [a, BandData.scale]
    ring
  have hplower : Real.exp (D.c₁ * D.scale x jstar) ≤ (p : ℝ) :=
    Nat.ceil_le.mp hplo
  have hrough : W x < (p : ℝ) := by
    calc
      W x < Real.exp (a * L x) := hxW
      _ = Real.exp (D.c₁ * D.scale x jstar) := by rw [harg]
      _ ≤ (p : ℝ) := hplower
  refine ⟨hpprime.pos, ?_⟩
  intro q hq hdiv
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hpprime).mp hdiv
  simpa [hqp] using hrough

/-- Positive reciprocal mass in every slot survives the one roughness
restriction, for each fixed exceptional index. -/
theorem harmonicQ_slot_product_lower (D : BandData) (hD : D.Valid)
    (k : ℝ) (hk : 0 < k)
    (hband : ∀ᶠ x : ℝ in atTop, ∀ j ≤ D.last x,
      k ≤ ∑ p ∈ D.band x j, (1 : ℝ) / p)
    (jstar : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (k ^ D.r₀ / (D.r₀.factorial : ℝ)) ^ (D.last x + 1) ≤
        D.harmonicQ x jstar := by
  have hrough := eventually_band_primes_rough D hD jstar
  filter_upwards [hband, hrough] with x hmass hrough
  let ms : D.Slot x → ℝ := fun s =>
    ∑ p ∈ D.slotValues x jstar s, (p : ℝ)⁻¹
  have hslot : ∀ s : D.Slot x, k ≤ ms s := by
    intro s
    have hj : s.1.val ≤ D.last x := by omega
    have hbandMass := hmass s.1.val hj
    by_cases he : s.1.val = jstar ∧ s.2.val = 0
    · have hsub : D.band x s.1.val ⊆ D.slotValues x jstar s := by
        intro p hp
        have hpI := (Finset.mem_filter.mp hp).1
        have hpR : rough (W x) p := hrough p (he.1 ▸ hp)
        have hpTarget := Finset.mem_filter.mpr ⟨hpI, hpR⟩
        simpa [BandData.slotValues, BandData.band, he] using hpTarget
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => show 0 ≤ (p : ℝ)⁻¹ by positivity)
      have hbandMass' : k ≤ ∑ p ∈ D.band x s.1.val, (p : ℝ)⁻¹ := by
        simpa only [one_div] using hbandMass
      have hsum' : ∑ p ∈ D.band x s.1.val, (p : ℝ)⁻¹ ≤ ms s := by
        simpa [ms] using hsum
      exact hbandMass'.trans hsum'
    · simpa only [ms, BandData.slotValues, if_neg he, one_div] using hbandMass
  have hprod : k ^ Fintype.card (D.Slot x) ≤ ∏ s, ms s := by
    calc
      k ^ Fintype.card (D.Slot x) = ∏ s : D.Slot x, k := by simp
      _ ≤ ∏ s : D.Slot x, ms s :=
        Finset.prod_le_prod₀ (fun s _ => hk.le) (fun s _ => hslot s)
  let n : ℕ := D.last x + 1
  have hcard : Fintype.card (D.Slot x) = n * D.r₀ := by
    simp [BandData.Slot, n]
  have hpowEq : (k ^ D.r₀) ^ n = k ^ Fintype.card (D.Slot x) := by
    rw [hcard, Nat.mul_comm, ← pow_mul]
  have hprod' : (k ^ D.r₀) ^ n ≤ ∏ s, ms s := by
    rw [hpowEq]
    exact hprod
  have hfactpos : 0 < (D.r₀.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos D.r₀
  let base : ℝ := k ^ D.r₀ / (D.r₀.factorial : ℝ)
  have hnorm :
      ((D.r₀.factorial : ℝ) ^ n)⁻¹ * (k ^ D.r₀) ^ n ≤ D.harmonicQ x jstar := by
    calc
      _ ≤ ((D.r₀.factorial : ℝ) ^ n)⁻¹ * ∏ s, ms s :=
        mul_le_mul_of_nonneg_left hprod' (inv_nonneg.mpr (pow_pos hfactpos _).le)
      _ = D.harmonicQ x jstar := by rfl
  have hbaseEq : base ^ n =
      ((D.r₀.factorial : ℝ) ^ n)⁻¹ * (k ^ D.r₀) ^ n := by
    dsimp [base]
    rw [div_pow]
    ring
  have hbaseQ : base ^ n ≤ D.harmonicQ x jstar := by
    rw [hbaseEq]
    exact hnorm
  exact hbaseQ

theorem harmonicQLowerTask_proof : Erdos821.P7Core.HarmonicQLowerTask := by
  intro hc D hD
  obtain ⟨k, hk, hkhalf, hband⟩ := eventually_pure_band_mass_lower D hD
  obtain ⟨Cb, hCb, hcount⟩ := Erdos821.S56Core.band_count_bound D hD
  let base : ℝ := k ^ D.r₀ / (D.r₀.factorial : ℝ)
  let M : ℝ := base⁻¹
  let C : ℝ := Cb * Real.log M
  have hfactpos : 0 < (D.r₀.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos D.r₀
  have hbasepos : 0 < base := div_pos (pow_pos hk _) hfactpos
  have hfact1 : 1 ≤ (D.r₀.factorial : ℝ) := by
    have hnat : 1 ≤ D.r₀.factorial := by
      have := Nat.factorial_pos D.r₀
      omega
    exact_mod_cast hnat
  have hkpow : k ^ D.r₀ ≤ 1 / 2 := by
    have hr₀ : D.r₀ ≠ 0 := by have := hD.1; omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hr₀
    rw [hm, pow_succ]
    calc
      k ^ m * k ≤ 1 * k :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hk.le (by linarith)) hk.le
      _ = k := one_mul _
      _ ≤ 1 / 2 := hkhalf
  have hbasele : base ≤ 1 / 2 := by
    dsimp [base]
    exact (div_le_self (pow_nonneg hk.le _) hfact1).trans hkpow
  have hbase_lt : base < 1 := hbasele.trans_lt (by norm_num)
  have hM : 1 ≤ M := by
    dsimp [M]
    rw [one_le_inv_iff₀]
    exact ⟨hbasepos, hbasele.trans (by norm_num)⟩
  have hMgt : 1 < M := by
    dsimp [M]
    exact (one_lt_inv₀ hbasepos).2 hbase_lt
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos hCb (Real.log_pos hMgt)
  refine ⟨C, hC, ?_⟩
  intro jstar
  have hbaseQ := harmonicQ_slot_product_lower D hD k hk hband jstar
  filter_upwards [hbaseQ, hcount,
      Erdos821.S56Core.tendsto_L.eventually (eventually_gt_atTop 0)]
      with x hbaseQ hnum hL
  let n : ℕ := D.last x + 1
  have hpoly := Erdos821.S56Core.polylog_of_loglog_count x Cb M n hL hM
    (by simpa [n] using hnum)
  have hMpow : 0 < M ^ n := pow_pos (by positivity) _
  have hLpow : 0 < L x ^ C := Real.rpow_pos_of_pos hL C
  have hinv := (inv_le_inv₀ hLpow hMpow).mpr hpoly
  have hlogpow : L x ^ (-C) ≤ (M ^ n)⁻¹ := by
    rw [Real.rpow_neg hL.le]
    exact hinv
  have hbaseM : (M ^ n)⁻¹ = base ^ n := by
    simp [M, inv_pow]
  rw [hbaseM] at hlogpow
  exact hlogpow.trans hbaseQ

example : Erdos821.P7Core.HarmonicQLowerTask := harmonicQLowerTask_proof

end Erdos821.P7Hq

