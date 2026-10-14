import Erdos821.P7.HarmonicMass
import Erdos821.P7.FreeWindowTask

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Every product tested against the compact cutoff has finite support in
the P-part. The multiplier can be arbitrary. -/
theorem cutoff_product_summable (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2)
    (x : ℝ) (hx : 0 < x) (v : ℕ) (hv : 0 < v) (f : ℕ → ℝ) :
    Summable (fun r : ℕ => f r * ((v : ℝ) * r) *
      C.psi (((v : ℝ) * r) / x)) := by
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (⌊2 * x⌋₊ + 1))).subset
  intro r hr
  by_contra hnot
  have hlarge : ⌊2 * x⌋₊ < r := by
    simp only [Finset.mem_coe, Finset.mem_range] at hnot
    omega
  have hp := psi_zero_of_product_gt C hpsi x hx v r
    (hlarge.trans_le (Nat.le_mul_of_pos_left r hv))
  simp only [Nat.cast_mul] at hp
  exact hr (by simp only [hp, mul_zero])

theorem freeWindow_weighted_summable (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2)
    (x : ℝ) (hx : 0 < x) (jstar : ℕ) (s : C.bands.Slot x)
    (v : ℕ) (hv : 0 < v) (f : ℕ → ℝ) :
    Summable (fun r : ℕ => f r * freeWindowKernel C x jstar s v r) := by
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (⌊2 * x⌋₊ + 1))).subset
  intro r hr
  by_contra hnot
  have hlarge : ⌊2 * x⌋₊ < r := by
    simp only [Finset.mem_coe, Finset.mem_range] at hnot
    omega
  have hz : freeWindowKernel C x jstar s v r = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    have hp := psi_zero_of_product_gt C hpsi x hx (p.val * v) r
      (hlarge.trans_le (Nat.le_mul_of_pos_left r
        (Nat.mul_pos (slotValue_pos C.bands p) hv)))
    simp only [Nat.cast_mul] at hp
    simp only [hp, mul_zero]
  exact hr (by simp only [hz, mul_zero])

/-- Exact conditioning on one Q coordinate. The factorial normalization and
the reciprocal weight of every remaining labelled coordinate are retained. -/
theorem candidate_mass_free_window (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2)
    (x : ℝ) (hx : 0 < x) (jstar : ℕ) (s : C.bands.Slot x)
    (hfree : ∀ z : C.bands.Lists x jstar,
      Erdos821.S56Core.GroupFree (C.bands.groups x) (C.bands.listProduct z)) :
    C.mass x jstar =
      ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        ∑ z : RestLists C.bands x jstar s, (restProduct C.bands z : ℝ)⁻¹ *
          ∑' r : ℕ, groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
            freeWindowKernel C x jstar s (restProduct C.bands z) r := by
  rw [candidate_mass_harmonic C hpsi x hx jstar hfree,
    harmonic_test_split C.bands x jstar s]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  simp only [listProduct_restoreList, Nat.cast_mul]
  have hs (p : C.bands.SlotValue x jstar s) : Summable (fun r : ℕ =>
      (p.val : ℝ)⁻¹ * (groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
        ((p.val : ℝ) * restProduct C.bands z * r) *
          C.psi (((p.val : ℝ) * restProduct C.bands z * r) / x))) := by
    simpa only [Nat.cast_mul] using
      (cutoff_product_summable C hpsi x hx (p.val * restProduct C.bands z)
        (Nat.mul_pos (slotValue_pos C.bands p) (restProduct_pos C.bands z))
        (groupHarmonicTerm C.bands.geometry (C.bands.groups x))).mul_left (p.val : ℝ)⁻¹
  calc
    _ = ∑ p : C.bands.SlotValue x jstar s, ∑' r : ℕ,
        (p.val : ℝ)⁻¹ * (groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
          ((p.val : ℝ) * restProduct C.bands z * r) *
            C.psi (((p.val : ℝ) * restProduct C.bands z * r) / x)) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (tsum_mul_left).symm
    _ = ∑' r : ℕ, ∑ p : C.bands.SlotValue x jstar s,
        (p.val : ℝ)⁻¹ * (groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
          ((p.val : ℝ) * restProduct C.bands z * r) *
            C.psi (((p.val : ℝ) * restProduct C.bands z * r) / x)) :=
      (Summable.tsum_finsetSum (fun p _ => hs p)).symm
    _ = _ := by
      apply tsum_congr
      intro r
      rw [freeWindowKernel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

theorem eventually_candidate_mass_free_window (C : CandidateData) (δ : ℝ)
    (hC : C.Geometry δ) :
    ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ, ∀ s : C.bands.Slot x,
      C.mass x jstar =
        ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
          ∑ z : RestLists C.bands x jstar s, (restProduct C.bands z : ℝ)⁻¹ *
            ∑' r : ℕ, groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
              freeWindowKernel C x jstar s (restProduct C.bands z) r := by
  rcases hC with ⟨hD, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hpsi, _, _⟩
  filter_upwards [eventually_listProduct_groupFree C.bands hD, eventually_gt_atTop 0]
    with x hx hx0
  exact fun jstar s => candidate_mass_free_window C hpsi x hx0 jstar s (hx jstar)

end Erdos821.P7Core

