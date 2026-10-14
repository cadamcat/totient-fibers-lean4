import Erdos821.P7.Positivity
import Erdos821.S56.SlotBounds
import Erdos821.S56.GeometricScales
import Erdos821.S56.GroupParts
import Erdos821.P6Mass.Mass
import Erdos821.P6Off.Rough
import Erdos821.S34.ScaleGrowth

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem exists_list_of_coefficient_ne_zero (D : BandData) (x : ℝ) (jstar v : ℕ)
    (hv : D.aQ x jstar v ≠ 0) : ∃ z : D.Lists x jstar, D.listProduct z = v := by
  unfold BandData.aQ at hv
  have hcard : (Finset.univ.filter (fun z : D.Lists x jstar => D.listProduct z = v)).card ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hv).2
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
  exact ⟨z, (Finset.mem_filter.mp hz).2⟩

theorem prime_dvd_group_or_free (G : PrimeGroups) (u : ℕ) (hu : 0 < u)
    (p : ℕ) (hp : p.Prime) (hpu : p ∣ u) :
    p ∈ Erdos821.S56Core.groupPrimes G ∨ p ∣ groupFreePart G u := by
  rw [← Erdos821.S56Core.groupPart_mul_freePart G u hu] at hpu
  rcases hp.dvd_mul.mp hpu with hpart | hfree
  · left
    unfold Erdos821.S56Core.groupPart at hpart
    obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hpart
    have hprime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1
    have heq : p = q := Nat.prime_eq_prime_of_dvd_pow hp hprime hpq
    exact heq ▸ (Finset.mem_inter.mp hq).2
  · exact Or.inr hfree

theorem eventually_exp_log_rpow_le (d δ : ℝ) (hd : d < 1) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.exp (L x ^ d) ≤ x ^ δ := by
  have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hd)).comp
    Erdos821.S56Core.tendsto_L
  filter_upwards [ht.eventually (eventually_lt_nhds hδ), eventually_gt_atTop (1 : ℝ)]
    with x hx hx1
  have hL : 0 < L x := Real.log_pos hx1
  have hpow : L x ^ (d - 1) ≤ δ := by
    convert hx.le using 1 <;> congr 1 <;> ring
  have hpower : L x ^ d ≤ δ * L x := by
    rw [Real.rpow_sub_one hL.ne'] at hpow
    exact (div_le_iff₀ hL).mp hpow
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx1)]
  exact Real.exp_le_exp.mpr (by simpa only [L, mul_comm] using hpower)

theorem band_scale_exp_upper (D : BandData) (hD : D.Valid) (δ x : ℝ)
    (hδ : D.c₂ * D.s' < δ) (hx : 1 < x) (j : ℕ) :
    Real.exp (D.c₂ * D.scale x j) ≤ x ^ δ := by
  have hL : 0 < L x := Real.log_pos hx
  have hc₂ : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
  have hscale := Erdos821.S56Core.scale_antitone D hD x hL 0 j (Nat.zero_le j)
  simp only [BandData.scale, pow_zero, div_one] at hscale
  have hnum : D.c₂ * D.scale x j ≤ (D.c₂ * D.s') * L x := by
    have h := mul_le_mul_of_nonneg_left hscale hc₂.le
    simpa only [BandData.scale, mul_assoc] using h
  calc
    _ ≤ Real.exp ((D.c₂ * D.s') * L x) := Real.exp_le_exp.mpr hnum
    _ = x ^ (D.c₂ * D.s') := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
      congr 1
      dsimp [L]
      ring
    _ ≤ x ^ δ := Real.rpow_le_rpow_of_exponent_le hx.le hδ.le

theorem logpower_eq_exp (x : ℝ) (hL : 0 < L x) :
    L x ^ (20 : ℕ) = Real.exp (20 * T x) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hL]
  simp only [T, Nat.cast_ofNat]
  congr 1
  ring

/-- The support condition holds uniformly in the slot index, including indices
past the last band, when all actual slots are pure primes. -/
theorem candidate_support_bounds (δ : ℝ) (C : CandidateData) (hC : C.Geometry δ) :
    ∀ᶠ x : ℝ in atTop, ∀ jstar u : ℕ, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x ∧
        ∀ p : ℕ, p.Prime → p ∣ u → L x ^ (20 : ℕ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ x ^ δ := by
  rcases hC with ⟨hD, _, _, _, _, hδ, hlast, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hsupp, _, _⟩
  let P := C.bands.geometry
  have hδpos : 0 < δ :=
    (mul_pos (hD.2.1.trans hD.2.2.1) hD.2.2.2.1).trans hδ
  have hPlo := Erdos821.S34Core.eventually_power_le_label_scale 20 P.a 1 P.ordered.1 zero_lt_one
  have hPup := eventually_exp_log_rpow_le P.d δ
    (by linarith [P.ordered.2.2.2.2]) hδpos
  have hW := Erdos821.P6Off.eventually_log_rpow_le_W 20
  have hDcopy := hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, hdata⟩ := hDcopy
  filter_upwards [hlast, hdata, hPlo, hPup, hW, eventually_gt_atTop (1 : ℝ),
    eventually_ge_atTop (Real.exp (Erdos821.P6Mass.thresh P))]
    with x ht hd hpl hpu hw hx hthreshold
  have hL : 0 < L x := Real.log_pos hx
  have hpl' : L x ^ (20 : ℕ) ≤ Real.exp (L x ^ P.a) := by
    norm_num only [one_mul, Real.rpow_ofNat] at hpl
    exact hpl
  have hw' : L x ^ (20 : ℕ) ≤ W x := by
    norm_num only [Real.rpow_ofNat] at hw
    exact hw
  intro jstar u hu
  obtain ⟨hux, hxu⟩ := weighted_interval_support C hsupp x (zero_lt_one.trans hx) jstar u hu
  have hu0 : 0 < u := by exact_mod_cast (zero_lt_one.trans hx).trans_le hux
  have hcoef : C.bands.aQ x jstar (groupFreePart (C.bands.groups x) u) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hu).1).1
  obtain ⟨z, hz⟩ := exists_list_of_coefficient_ne_zero C.bands x jstar _ hcoef
  refine ⟨hux, hxu, ?_⟩
  intro p hp hdiv
  rcases prime_dvd_group_or_free (C.bands.groups x) u hu0 p hp hdiv with hgroup | hfree
  · obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hgroup
    exact ⟨hpl'.trans (Erdos821.P6Mass.prime_ge_exp_a hthreshold hd.1 hpg),
      (Erdos821.P6Mass.prime_le_exp_d hthreshold hd.1 hpg).trans hpu⟩
  · rw [← hz] at hfree
    obtain ⟨s, _, hps⟩ := hp.prime.exists_mem_finset_dvd hfree
    have hslot := Erdos821.S56Core.slot_value_bounds C.bands z s
    have hup : ((z s).val : ℝ) ≤ x ^ δ := hslot.2.trans
      (band_scale_exp_upper C.bands hD δ x hδ hx s.1.val)
    have hps' : (p : ℝ) ≤ (z s).val := by
      exact_mod_cast Nat.le_of_dvd (Erdos821.S56Core.slot_value_pos C.bands z s) hps
    refine ⟨?_, hps'.trans hup⟩
    have hmem := (z s).property
    by_cases he : s.1.val = jstar ∧ s.2.val = 0
    · simp only [BandData.slotValues, he, ite_true] at hmem
      exact hw'.trans ((Finset.mem_filter.mp hmem).2.2 p hp hps).le
    · simp only [BandData.slotValues, he, ite_false] at hmem
      have hprime : ((z s).val).Prime := (Finset.mem_filter.mp hmem).2
      have heq : p = (z s).val := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hps
      have hs : C.bands.scale x (C.bands.last x) ≤ C.bands.scale x s.1.val :=
        Erdos821.S56Core.scale_antitone C.bands hD x hL s.1.val (C.bands.last x)
          (Nat.le_of_lt_succ s.1.isLt)
      have hlog : 20 * T x ≤ C.bands.c₁ * C.bands.scale x s.1.val :=
        ht.1.trans (mul_le_mul_of_nonneg_left hs hD.2.1.le)
      rw [logpower_eq_exp x hL, heq]
      exact (Real.exp_le_exp.mpr hlog).trans hslot.1

end Erdos821.P7Core

