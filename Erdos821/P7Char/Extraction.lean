import Erdos821.P7Char.Task
import Erdos821.S56.GroupParts

/-! Extraction of one pure slot from the candidate weight:
`weight(u) = ∑_{p ∈ slot, p ∣ u} β(u/p)`, and the resulting bilinear form. -/
noncomputable section
open scoped BigOperators Pointwise
open Filter Erdos821.Blueprint.Analytic

namespace Erdos821.P7Char

open Erdos821.Blueprint Erdos821.P7B

variable (D : BandData)

def normQ (x : ℝ) : ℝ := ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹

theorem normQ_nonneg (x : ℝ) : 0 ≤ normQ D x := by
  unfold normQ; positivity

def restCount (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x) (m : ℕ) : ℝ :=
  normQ D x * (Fintype.card {z : RestLists D x jstar s₀ // restProduct D x jstar s₀ z = m} : ℝ)

/-- Coefficient of the complementary variable after extracting slot `s₀`. -/
def beta (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x) (r : ℕ) : ℝ :=
  restCount D x jstar s₀ (groupFreePart (D.groups x) r) *
    markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) r

theorem restCount_nonneg (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x) (m : ℕ) :
    0 ≤ restCount D x jstar s₀ m :=
  mul_nonneg (normQ_nonneg D x) (Nat.cast_nonneg _)

theorem beta_nonneg (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x) (r : ℕ) :
    0 ≤ beta D x jstar s₀ r :=
  mul_nonneg (restCount_nonneg D x jstar s₀ _)
    (S56Core.markWeight_nonneg _ _ D.geometry.damping.1.le _ r)

theorem aQ_eq_sum_slotValues (x : ℝ) (jstar v : ℕ) (s₀ : D.Slot x) :
    D.aQ x jstar v = ∑ p ∈ D.slotValues x jstar s₀,
      normQ D x * (Fintype.card
        {z : RestLists D x jstar s₀ // p * restProduct D x jstar s₀ z = v} : ℝ) := by
  rw [aQ_eq_slotFiber_sum D x jstar v s₀, Finset.mul_sum]
  exact (Finset.sum_subtype (D.slotValues x jstar s₀) (fun _ => Iff.rfl)
    (fun p => normQ D x * (Fintype.card
      {z : RestLists D x jstar s₀ // p * restProduct D x jstar s₀ z = v} : ℝ))).symm

theorem card_slot_fiber (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x) (p u : ℕ) (hp : p.Prime)
    (hfree : S56Core.GroupFree (D.groups x) p) (hu : 0 < u) :
    Fintype.card {z : RestLists D x jstar s₀ //
        p * restProduct D x jstar s₀ z = groupFreePart (D.groups x) u} =
      if p ∣ u then Fintype.card {z : RestLists D x jstar s₀ //
        restProduct D x jstar s₀ z = groupFreePart (D.groups x) (u / p)} else 0 := by
  split_ifs with hpu
  · have hq : 0 < u / p := Nat.div_pos (Nat.le_of_dvd hu hpu) hp.pos
    have hg : groupFreePart (D.groups x) u = p * groupFreePart (D.groups x) (u / p) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hpu]
      exact S56Core.groupFreePart_mul _ p (u / p) hp.pos hq hfree
    rw [hg]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight
      (fun z => ⟨fun h => Nat.eq_of_mul_eq_mul_left hp.pos h, fun h => by rw [h]⟩)
  · rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨z, hz⟩
    exact hpu ((Dvd.intro _ hz).trans (S56Core.groupFreePart_dvd _ u hu))

theorem weight_extract (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x)
    (hB : ∀ p ∈ D.slotValues x jstar s₀, p.Prime ∧ S56Core.GroupFree (D.groups x) p)
    (u : ℕ) (hu : 0 < u) :
    D.weight x jstar u = ∑ p ∈ D.slotValues x jstar s₀,
      if p ∣ u then beta D x jstar s₀ (u / p) else 0 := by
  unfold BandData.weight
  rw [aQ_eq_sum_slotValues D x jstar _ s₀, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨hpp, hfree⟩ := hB p hp
  rw [card_slot_fiber D x jstar s₀ p u hpp hfree hu]
  split_ifs with hpu
  · unfold beta restCount
    have hm : markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u =
        markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) (u / p) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hpu]
      exact S56Core.markWeight_mul _ p (u / p) hfree _ _
    rw [hm]
  · simp

theorem psi_eq_zero_of_gt (psi : ℝ → ℝ) (hψ : Function.support psi ⊆ Set.Icc 1 2)
    (y : ℝ) (hy : 2 < y) : psi y = 0 := by
  by_contra h
  have := (hψ (Function.mem_support.2 h)).2
  linarith

theorem weighted_sum_extract (C : CandidateData) (x : ℝ) (hx : 0 < x) (jstar : ℕ)
    (s₀ : C.bands.Slot x)
    (hB : ∀ p ∈ C.bands.slotValues x jstar s₀,
      p.Prime ∧ S56Core.GroupFree (C.bands.groups x) p)
    (hψ : Function.support C.psi ⊆ Set.Icc 1 2)
    (F : ℕ → ℂ) (N : ℕ → ℕ) (hN : ∀ p ∈ C.bands.slotValues x jstar s₀, ⌊2 * x⌋₊ / p ≤ N p) :
    ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, (C.weighted x jstar u : ℂ) * F u =
      ∑ p ∈ C.bands.slotValues x jstar s₀, ∑ r ∈ Finset.Icc 1 (N p),
        (beta C.bands x jstar s₀ r : ℂ) * (C.psi ((p : ℝ) * r / x) : ℂ) * F (p * r) := by
  set M := ⌊2 * x⌋₊ with hM
  have h1 : ∀ u ∈ Finset.Icc 1 M, (C.weighted x jstar u : ℂ) * F u =
      ∑ p ∈ C.bands.slotValues x jstar s₀,
        if p ∣ u then (beta C.bands x jstar s₀ (u / p) : ℂ) * (C.psi ((u : ℝ) / x) : ℂ) * F u
        else 0 := by
    intro u hu
    have hu0 : 0 < u := (Finset.mem_Icc.1 hu).1
    unfold CandidateData.weighted
    rw [weight_extract C.bands x jstar s₀ hB u hu0, Complex.ofReal_mul, Complex.ofReal_sum,
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨hpp, _⟩ := hB p hp
  rw [← Finset.sum_filter]
  have hbij : ∑ u ∈ (Finset.Icc 1 M).filter (fun u => p ∣ u),
      (beta C.bands x jstar s₀ (u / p) : ℂ) * (C.psi ((u : ℝ) / x) : ℂ) * F u =
      ∑ r ∈ Finset.Icc 1 (M / p),
        (beta C.bands x jstar s₀ r : ℂ) * (C.psi ((p : ℝ) * r / x) : ℂ) * F (p * r) := by
    apply Finset.sum_nbij' (fun u => u / p) (fun r => p * r)
    · intro u hu
      obtain ⟨huI, hpu⟩ := Finset.mem_filter.1 hu
      obtain ⟨hu1, huM⟩ := Finset.mem_Icc.1 huI
      exact Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd hu1 hpu) hpp.pos,
        Nat.div_le_div_right huM⟩
    · intro r hr
      obtain ⟨hr1, hrM⟩ := Finset.mem_Icc.1 hr
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, dvd_mul_right p r⟩
      · exact Nat.mul_pos hpp.pos hr1
      · calc p * r ≤ p * (M / p) := Nat.mul_le_mul_left p hrM
          _ ≤ M := Nat.mul_div_le M p
    · intro u hu
      exact Nat.mul_div_cancel' (Finset.mem_filter.1 hu).2
    · intro r _
      exact Nat.mul_div_cancel_left r hpp.pos
    · intro u hu
      have hpu := (Finset.mem_filter.1 hu).2
      have hu' : p * (u / p) = u := Nat.mul_div_cancel' hpu
      have hcast : ((u : ℕ) : ℝ) = (p : ℝ) * ((u / p : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, hu']
      rw [hu', hcast]
  rw [hbij]
  apply Finset.sum_subset
  · intro r hr
    obtain ⟨hr1, hrM⟩ := Finset.mem_Icc.1 hr
    exact Finset.mem_Icc.2 ⟨hr1, hrM.trans (hN p hp)⟩
  · intro r hr hnot
    obtain ⟨hr1, _⟩ := Finset.mem_Icc.1 hr
    have hgt : M / p < r := by
      by_contra hle
      exact hnot (Finset.mem_Icc.2 ⟨hr1, not_lt.1 hle⟩)
    have hMlt : M < p * r := by
      have := (Nat.div_lt_iff_lt_mul hpp.pos).1 hgt
      linarith [mul_comm r p]
    have h2x : 2 * x < ((p * r : ℕ) : ℝ) := by
      have h2x0 : 0 ≤ 2 * x := by linarith
      exact (Nat.floor_lt h2x0).1 hMlt
    have hz : C.psi ((p : ℝ) * r / x) = 0 := by
      apply psi_eq_zero_of_gt C.psi hψ
      rw [lt_div_iff₀ hx]
      push_cast at h2x
      linarith
    rw [hz]
    simp

/-! ### Coefficient bounds -/

theorem card_divisors_prime_mul_le (p m : ℕ) (hp : p.Prime) :
    ((p * m).divisors.card : ℝ) ≤ 2 * (m.divisors.card : ℝ) := by
  have h := Finset.card_mul_le (s := p.divisors) (t := m.divisors)
  rw [← Nat.divisors_mul, Nat.Prime.divisors hp, Finset.card_pair hp.one_lt.ne] at h
  exact_mod_cast h

theorem restCount_le_aQ (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x) (p₀ : ℕ)
    (hp₀ : p₀ ∈ D.slotValues x jstar s₀) (hp₀pos : 0 < p₀) (m : ℕ) :
    restCount D x jstar s₀ m ≤ D.aQ x jstar (p₀ * m) := by
  rw [aQ_eq_sum_slotValues D x jstar (p₀ * m) s₀]
  have hterm : restCount D x jstar s₀ m = normQ D x * (Fintype.card
      {z : RestLists D x jstar s₀ // p₀ * restProduct D x jstar s₀ z = p₀ * m} : ℝ) := by
    unfold restCount
    congr 2
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight
      (fun z => ⟨fun h => by rw [h], fun h => Nat.eq_of_mul_eq_mul_left hp₀pos h⟩)
  rw [hterm]
  exact Finset.single_le_sum (f := fun p => normQ D x * (Fintype.card
      {z : RestLists D x jstar s₀ // p * restProduct D x jstar s₀ z = p₀ * m} : ℝ))
    (fun p _ => mul_nonneg (normQ_nonneg D x) (Nat.cast_nonneg _)) hp₀

theorem beta_divisor_bound (hD : D.Valid) :
    ∃ E : ℝ, 0 < E ∧ ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop, ∀ s₀ : D.Slot x,
      ∀ p₀ ∈ D.slotValues x jstar s₀, p₀.Prime → ∀ r : ℕ, 0 < r →
        beta D x jstar s₀ r ≤ 2 * L x ^ E * (r.divisors.card : ℝ) := by
  obtain ⟨E, hE, hmark⟩ := Erdos821.P6Sq.markWeight_log_bound D.geometry
  refine ⟨E, hE, ?_⟩
  intro jstar
  have hslot := Erdos821.P6Slot.slotMultiplicityTask_proof D hD jstar
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, hevent⟩ := hD
  filter_upwards [hslot, hmark, hevent,
    S56Core.tendsto_L.eventually (eventually_gt_atTop 0)] with x hx hm hvalid hL
  intro s₀ p₀ hp₀ hpp r hr
  have hmw := hm (D.groups x) hvalid.1 r
  have hmw0 := S56Core.markWeight_nonneg (D.groups x) D.geometry.q D.geometry.damping.1.le
    (fun _ => D.geometry.ell) r
  have hrc := restCount_le_aQ D x jstar s₀ p₀ hp₀ hpp.pos (groupFreePart (D.groups x) r)
  have haq := hx (p₀ * groupFreePart (D.groups x) r)
  have hdiv := card_divisors_prime_mul_le p₀ (groupFreePart (D.groups x) r) hpp
  have hgfp : ((groupFreePart (D.groups x) r).divisors.card : ℝ) ≤ r.divisors.card := by
    exact_mod_cast Finset.card_le_card
      (Nat.divisors_subset_of_dvd hr.ne' (S56Core.groupFreePart_dvd (D.groups x) r hr))
  have hrc' : restCount D x jstar s₀ (groupFreePart (D.groups x) r) ≤
      2 * (r.divisors.card : ℝ) := by linarith
  have hLE : 0 ≤ L x ^ E := Real.rpow_nonneg hL.le _
  calc beta D x jstar s₀ r
      = restCount D x jstar s₀ (groupFreePart (D.groups x) r) *
          markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) r := rfl
    _ ≤ (2 * (r.divisors.card : ℝ)) * L x ^ E :=
        mul_le_mul hrc' hmw hmw0 (by positivity)
    _ = 2 * L x ^ E * (r.divisors.card : ℝ) := by ring

/-! ### The first slot -/

theorem band_zero_prime_free (hD : D.Valid) :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ D.band x 0, p.Prime ∧ S56Core.GroupFree (D.groups x) p := by
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, hevent⟩ := hD
  filter_upwards [hevent] with x hx
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2
  refine ⟨hpp, ?_⟩
  intro q hq hqp
  obtain ⟨g, _, hqg⟩ := Finset.mem_biUnion.1 hq
  have hqprime := (D.groups x).prime g q hqg
  have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpp).1 hqp
  subst hqe
  exact Finset.disjoint_left.1 (hx.2.2.2.2 0 (Nat.zero_le _) g) hp hqg

theorem band_zero_bounds (x : ℝ) (p : ℕ) (hp : p ∈ D.band x 0) :
    Real.exp (D.c₁ * D.scale x 0) ≤ p ∧ (p : ℝ) ≤ Real.exp (D.c₂ * D.scale x 0) := by
  have hI := (Finset.mem_filter.1 hp).1
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hI
  exact ⟨Nat.ceil_le.1 h1, (Nat.le_floor_iff (Real.exp_pos _).le).1 h2⟩

end Erdos821.P7Char
