import Erdos821.P7.FreeCoordinate
import Erdos821.P7Band.Dyadic
import Erdos821.S56.HarmonicQBound

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem zero_slotValues_eq_band (C : CandidateData) (δ : ℝ) (hC : C.Geometry δ)
    (x : ℝ) (jstar : ℕ) (hj : C.j₀ ≤ jstar) (s : C.bands.Slot x)
    (hs : s.1.val = 0) : C.bands.slotValues x jstar s = C.bands.band x 0 := by
  have hprefix := hC.2.2.2.2.2.2.2.1
  have hjpos : 0 < jstar := by omega
  have he : ¬(s.1.val = jstar ∧ s.2.val = 0) := by omega
  unfold BandData.slotValues
  rw [ite_eq_right he, hs]

/-- A fixed positive lower and upper mass for every band-zero slot. Since
the exceptional band is beyond the prefix, every such slot is pure. -/
theorem free_slot_harmonic_bounds (hc : ClassicalInputs) (C : CandidateData)
    (δ : ℝ) (hC : C.Geometry δ) :
    ∃ k M : ℝ, 0 < k ∧ 1 ≤ M ∧ ∀ᶠ x : ℝ in atTop,
      ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ s : C.bands.Slot x, s.1.val = 0 →
        k ≤ slotHarmonic C.bands x jstar s ∧ slotHarmonic C.bands x jstar s ≤ M := by
  obtain ⟨Y, hY⟩ := Erdos821.P7Band.grp_mass_eventually
  obtain ⟨M, hM, hu⟩ := Erdos821.S56Core.band_harmonic_uniform hc C.bands hC.1
  have hc1 : C.bands.c₁ = 1 := hC.2.1
  have hc2 : C.bands.c₂ = 6 / 5 := hC.2.2.1
  have hs : 0 < C.bands.s' := hC.1.2.2.2.1
  refine ⟨Real.log (6 / 5) / 2, M, by
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num), hM, ?_⟩
  filter_upwards [hu, Erdos821.S56Core.tendsto_L.eventually
    (eventually_ge_atTop (max 1 (Y / C.bands.s')))] with x hupper hL
  have hL1 : 1 ≤ L x := (le_max_left _ _).trans hL
  have hscale : 0 < C.bands.scale x 0 := by
    simpa only [BandData.scale, pow_zero, div_one] using
      mul_pos hs (zero_lt_one.trans_le hL1)
  have hYscale : Y ≤ C.bands.scale x 0 := by
    have h := (div_le_iff₀ hs).mp ((le_max_right _ _).trans hL)
    simpa only [BandData.scale, pow_zero, div_one, mul_comm] using h
  have hYexp : Y ≤ Real.exp (3 / 2 * (2 / 3 * C.bands.scale x 0)) := by
    have heq : (3 / 2 : ℝ) * (2 / 3 * C.bands.scale x 0) = C.bands.scale x 0 := by ring
    rw [heq]
    linarith [Real.add_one_le_exp (C.bands.scale x 0)]
  have hlower := (hY (2 / 3 * C.bands.scale x 0) (by positivity) hYexp).1
  have hsub : Erdos821.P7Band.grp (2 / 3 * C.bands.scale x 0) ⊆
      C.bands.band x 0 := by
    intro p hp
    obtain ⟨hpp, hlo, hhi⟩ := Erdos821.P7Band.mem_grp.mp hp
    have hlo' : Real.exp (C.bands.scale x 0) ≤ (p : ℝ) := by
      have heq : (3 / 2 : ℝ) * (2 / 3 * C.bands.scale x 0) = C.bands.scale x 0 := by ring
      rw [heq] at hlo
      exact hlo.le
    have hhi' : (p : ℝ) ≤ Real.exp (6 / 5 * C.bands.scale x 0) := by
      have heq : (9 / 5 : ℝ) * (2 / 3 * C.bands.scale x 0) =
          6 / 5 * C.bands.scale x 0 := by ring
      rwa [heq] at hhi
    simp only [BandData.band, hc1, hc2, one_mul, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.ceil_le.mpr hlo', (Nat.le_floor_iff (Real.exp_pos _).le).mpr hhi'⟩, hpp⟩
  intro jstar hj s hs0
  rw [slotHarmonic, zero_slotValues_eq_band C δ hC x jstar hj s hs0]
  constructor
  · have he : Real.log (6 / 5) / 2 ≤
        ∑ p ∈ Erdos821.P7Band.grp (2 / 3 * C.bands.scale x 0), (p : ℝ)⁻¹ := by
      simpa only [one_div] using hlower
    exact he.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity))
  · exact hupper 0 (Nat.zero_le _)

theorem slotValue_nonempty_of_harmonic_pos (D : BandData) (x : ℝ) (jstar : ℕ)
    (s : D.Slot x) (hp : 0 < slotHarmonic D x jstar s) :
    Nonempty (D.SlotValue x jstar s) := by
  have hne : D.slotValues x jstar s ≠ ∅ := by
    intro he
    simp only [slotHarmonic, he, Finset.sum_empty, lt_self_iff_false] at hp
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact ⟨⟨v, hv⟩⟩

/-- Transport the prefix fraction to the complementary coordinates by
cancelling their common positive free-slot mass. -/
theorem prefix_fraction_rest (C : CandidateData) (epsilon c x : ℝ) (jstar : ℕ)
    (s : C.bands.Slot x) (hslot : 0 < slotHarmonic C.bands x jstar s)
    (hfull : c * (∑ z : C.bands.Lists x jstar, (C.bands.listProduct z : ℝ)⁻¹) ≤
      ∑ z : C.bands.Lists x jstar, if prefixMidpointEvent C epsilon s z then
        (C.bands.listProduct z : ℝ)⁻¹ else 0) :
    c * restHarmonic C.bands x jstar s ≤
      ∑ z : RestLists C.bands x jstar s,
        if restPrefixEvent C epsilon s z then (restProduct C.bands z : ℝ)⁻¹ else 0 := by
  have ht := harmonic_test_split C.bands x jstar s (fun _ => 1)
  simp only [mul_one, ← Finset.sum_mul, ← slotHarmonic_eq_subtype_sum] at ht
  change (∑ z : C.bands.Lists x jstar, (C.bands.listProduct z : ℝ)⁻¹) =
    restHarmonic C.bands x jstar s * slotHarmonic C.bands x jstar s at ht
  rw [ht, prefix_harmonic_free_split] at hfull
  exact (mul_le_mul_iff_right₀ hslot).mp
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hfull)

end Erdos821.P7Core

