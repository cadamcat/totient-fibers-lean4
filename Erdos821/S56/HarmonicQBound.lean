import Erdos821.S56.HarmonicQ
import Erdos821.S56.PrimeHarmonicBand
import Erdos821.S56.GeometricScales
import Erdos821.S56.PureCoefficients

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem integer_interval_harmonic_le (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (P : ℕ → Prop) [DecidablePred P] :
    reciprocalMass ((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter P) ≤ 1 + Real.log hi := by
  have hN : 1 ≤ ⌊hi⌋₊ := (Nat.one_le_floor_iff hi).mpr hhi
  have hsub : (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter P ⊆ Finset.Icc 1 ⌊hi⌋₊ := by
    intro v hv
    obtain ⟨hvlo, hvhi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1
    have hp : (0 : ℝ) < v := hlo.trans_le (Nat.ceil_le.mp hvlo)
    have hv1 : 1 ≤ v := by exact_mod_cast hp
    exact Finset.mem_Icc.mpr ⟨hv1, hvhi⟩
  have hlog : Real.log (⌊hi⌋₊ : ℝ) ≤ Real.log hi :=
    Real.log_le_log (by exact_mod_cast (zero_lt_one.trans_le hN))
      (Nat.floor_le (zero_le_one.trans hhi))
  calc
    _ ≤ ∑ v ∈ Finset.Icc 1 ⌊hi⌋₊, (v : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => by positivity)
    _ ≤ 1 + Real.log (⌊hi⌋₊ : ℝ) := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
        harmonic_le_one_add_log ⌊hi⌋₊
    _ ≤ _ := add_le_add le_rfl hlog

theorem band_harmonic_uniform (hc : ClassicalInputs) (D : BandData) (hD : D.Valid) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ᶠ x : ℝ in atTop, ∀ j ≤ D.last x,
      reciprocalMass (D.band x j) ≤ M := by
  obtain ⟨K, hK⟩ := hc.mertens.1
  have hm : ∀ y : ℝ, 2 ≤ y → |reciprocalMass (primesUpTo y) - Real.log (Real.log y)| ≤ K := hK
  let M := max 1 (Real.log (2 * D.c₂ / D.c₁) + 2 * K)
  have hdata := hD
  obtain ⟨_, hc1, hc12, _, _, _, _, _, cmin, cmax, hcmin, hcmax, hevent⟩ := hdata
  refine ⟨M, le_max_left _ _, ?_⟩
  filter_upwards [hevent, tendsto_T.eventually (eventually_ge_atTop ((Real.log 4 / D.c₁) / cmin)),
    tendsto_L.eventually (eventually_gt_atTop 0)] with x hx hT hL
  intro j hj
  have hscale : Real.log 4 / D.c₁ ≤ D.scale x j := by
    have hbound : Real.log 4 / D.c₁ ≤ cmin * T x := by
      have h := (div_le_iff₀ hcmin).mp hT
      simpa only [mul_comm] using h
    exact (hbound.trans hx.2.1).trans (scale_antitone D hD x hL j (D.last x) hj)
  have hlarge : Real.log 4 ≤ D.c₁ * D.scale x j := by
    simpa only [mul_comm] using (div_le_iff₀ hc1).mp hscale
  have hpr (p : ℕ) (hp : p ∈ D.band x j) :
      p.Prime ∧ Real.exp (D.c₁ * D.scale x j) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ Real.exp (D.c₂ * D.scale x j) := by
    obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hI
    exact ⟨hprime, Nat.ceil_le.mp hlo, (Nat.le_floor_iff (Real.exp_pos _).le).mp hhi⟩
  exact (prime_harmonic_band K D.c₁ D.c₂ (D.scale x j) hm hc1 hc12
    (scale_pos D hD x hL j) hlarge (D.band x j) hpr).trans (le_max_right _ _)

theorem rough_band_harmonic_le (D : BandData) (hD : D.Valid) (x : ℝ) (hL : 1 ≤ L x) (j : ℕ) :
    reciprocalMass ((Finset.Icc ⌈Real.exp (D.c₁ * D.scale x j)⌉₊
      ⌊Real.exp (D.c₂ * D.scale x j)⌋₊).filter (rough (W x))) ≤ 2 * L x := by
  have hc2 : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
  have hs : 0 < D.scale x j := scale_pos D hD x (zero_lt_one.trans_le hL) j
  have hhi : 1 ≤ Real.exp (D.c₂ * D.scale x j) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_pos hc2 hs).le
  have hpow : 1 ≤ D.ratio ^ j := one_le_pow₀ hD.2.2.2.2.1.le
  have hsize : D.c₂ * D.scale x j ≤ L x / 4 := by
    have hc := hD.2.2.2.2.2.1
    have hnum0 : 0 ≤ D.c₂ * D.s' := mul_nonneg hc2.le hD.2.2.2.1.le
    have hdiv : D.c₂ * D.s' / D.ratio ^ j ≤ D.c₂ * D.s' :=
      (div_le_self hnum0 hpow)
    have h := mul_le_mul_of_nonneg_right (hdiv.trans hc.le) (zero_le_one.trans hL)
    convert h using 1
    · unfold BandData.scale; ring
    · ring
  have h := integer_interval_harmonic_le (Real.exp (D.c₁ * D.scale x j))
    (Real.exp (D.c₂ * D.scale x j)) (Real.exp_pos _) hhi (rough (W x))
  rw [Real.log_exp] at h
  linarith


/-- The harmonic cost of all labelled slots is polynomial in L, uniformly
in the exceptional band. At most one slot contributes the extra O(L). -/
theorem harmonicQ_polylog (hc : ClassicalInputs) (D : BandData) (hD : D.Valid) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ,
      D.harmonicQ x jstar ≤ L x ^ C := by
  obtain ⟨M, hM, hband⟩ := band_harmonic_uniform hc D hD
  obtain ⟨Cb, hCb, hcount⟩ := band_count_bound D hD
  let Cf := Cb * D.r₀ * Real.log M
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  refine ⟨Cf + 2, by dsimp [Cf]; positivity, ?_⟩
  filter_upwards [hband, hcount, tendsto_L.eventually (eventually_ge_atTop 2)] with x hx hb hL
  intro jstar
  let ms : D.Slot x → ℝ := fun s => reciprocalMass (D.slotValues x jstar s)
  let ex : D.Slot x → Prop := fun s => s.1.val = jstar ∧ s.2.val = 0
  have hslot (s : D.Slot x) : ms s ≤ M * (if ex s then 2 * L x else 1) := by
    by_cases he : ex s
    · have hmass := rough_band_harmonic_le D hD x (by linarith) s.1.val
      change s.1.val = jstar ∧ s.2.val = 0 at he
      have hbound := hmass.trans (by
        have h := mul_le_mul_of_nonneg_right hM (by linarith : 0 ≤ 2 * L x)
        simpa only [one_mul] using h)
      simpa only [ms, BandData.slotValues, ex, he, true_and, ite_true] using hbound
    · have hmass := hx s.1.val (Nat.le_of_lt_succ s.1.isLt)
      change ¬(s.1.val = jstar ∧ s.2.val = 0) at he
      simpa only [ms, BandData.slotValues, ex, he, ite_false, mul_one] using hmass
  have hm0 (s : D.Slot x) : 0 ≤ ms s := Finset.sum_nonneg (fun v _ => by positivity)
  have hbranches : (Finset.univ.filter ex).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨hb1, hb2⟩ := (Finset.mem_filter.mp hb).2
    apply Prod.ext <;> apply Fin.ext
    · exact ha1.trans hb1.symm
    · exact ha2.trans hb2.symm
  have hproduct : (∏ s, ms s) ≤ M ^ Fintype.card (D.Slot x) * (2 * L x) := by
    calc
      _ ≤ ∏ s : D.Slot x, M * (if ex s then 2 * L x else 1) :=
        Finset.prod_le_prod₀ (fun s _ => hm0 s) (fun s _ => hslot s)
      _ = M ^ Fintype.card (D.Slot x) * (2 * L x) ^ (Finset.univ.filter ex).card := by
        rw [Finset.prod_mul_distrib]
        rw [Finset.prod_ite (s := Finset.univ) (p := ex)
          (fun _ : D.Slot x => 2 * L x) (fun _ => 1)]
        simp only [Finset.prod_const, Finset.card_univ, one_pow, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ 2 * L x) hbranches)
        (pow_nonneg (zero_le_one.trans hM) _)
  have hslots : ((Fintype.card (D.Slot x) : ℕ) : ℝ) ≤ (Cb * D.r₀) * T x := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have h := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg D.r₀ : (0 : ℝ) ≤ D.r₀)
    simpa [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have hcost := polylog_of_loglog_count x (Cb * D.r₀) M _ (by linarith) hM hslots
  obtain ⟨hmu0, hmu⟩ := factorial_normalization_le_one D x
  have hms0 : 0 ≤ ∏ s, ms s := Finset.prod_nonneg (fun s _ => hm0 s)
  change ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ * (∏ s, ms s) ≤ _
  calc
    _ ≤ ∏ s, ms s := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu hms0
    _ ≤ M ^ Fintype.card (D.Slot x) * (2 * L x) := hproduct
    _ ≤ L x ^ Cf * (2 * L x) := mul_le_mul_of_nonneg_right hcost (by linarith)
    _ ≤ L x ^ Cf * (L x) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left (by nlinarith : 2 * L x ≤ L x ^ 2) (Real.rpow_nonneg (by linarith) _)
    _ = L x ^ (Cf + 2) := by rw [Real.rpow_add (by linarith : 0 < L x), Real.rpow_two]


end Erdos821.S56Core
