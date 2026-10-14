import Erdos821.P7.LiteralMass
import Erdos821.P7.HarmonicP

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem psi_zero_of_product_gt (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2)
    (x : ℝ) (hx : 0 < x) (v r : ℕ) (hlarge : ⌊2 * x⌋₊ < v * r) :
    C.psi ((v * r : ℕ) / x) = 0 := by
  by_contra hne
  have hupper := (hpsi hne).2
  have hreal : 2 * x < (v * r : ℕ) := Nat.lt_of_floor_lt hlarge
  have hbound := (div_le_iff₀ hx).mp hupper
  linarith

/-- Multiply the two harmonic measures by the full product to recover the
ordinary candidate mass. Compact support makes the inner sum finite. -/
theorem candidate_mass_harmonic (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2)
    (x : ℝ) (hx : 0 < x) (jstar : ℕ)
    (hfree : ∀ z : C.bands.Lists x jstar,
      Erdos821.S56Core.GroupFree (C.bands.groups x) (C.bands.listProduct z)) :
    C.mass x jstar =
      ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        ∑ z : C.bands.Lists x jstar, (C.bands.listProduct z : ℝ)⁻¹ *
          ∑' r : ℕ,
            groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
              ((C.bands.listProduct z : ℝ) * r) *
                C.psi (((C.bands.listProduct z : ℝ) * r) / x) := by
  rw [candidate_mass_product C x jstar hfree]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  let v := C.bands.listProduct z
  have hv : 0 < v := listProduct_pos C.bands z
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvne : (C.bands.listProduct z : ℝ) ≠ 0 := hvR.ne'
  have htsum : (∑' r : ℕ,
      groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
        ((v : ℝ) * r) * C.psi (((v : ℝ) * r) / x)) =
      ∑ r ∈ Finset.Icc 1 ⌊2 * x⌋₊,
        groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
          ((v : ℝ) * r) * C.psi (((v : ℝ) * r) / x) := by
    apply tsum_eq_sum
    intro r hr
    by_cases hr0 : r = 0
    · simp [hr0, groupHarmonicTerm]
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hrlarge : ⌊2 * x⌋₊ < r := by
        have hi : ¬(1 ≤ r ∧ r ≤ ⌊2 * x⌋₊) := by simpa only [Finset.mem_Icc] using hr
        omega
      have hlarge : ⌊2 * x⌋₊ < v * r :=
        hrlarge.trans_le (Nat.le_mul_of_pos_left r hv)
      have hp := psi_zero_of_product_gt C hpsi x hx v r hlarge
      simp only [Nat.cast_mul] at hp
      rw [hp, mul_zero]
  change _ = (v : ℝ)⁻¹ * _
  rw [htsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  by_cases hpure : groupFreePart (C.bands.groups x) r = 1
  · by_cases hsize : v * r ≤ ⌊2 * x⌋₊
    · simp only [v, hpure, hsize, and_self, ite_true, groupHarmonicTerm, hrpos,
        Nat.cast_mul]
      field_simp [hvne, hrR.ne'] <;> ring
    · have hp := psi_zero_of_product_gt C hpsi x hx v r (Nat.lt_of_not_ge hsize)
      simp only [Nat.cast_mul] at hp
      simp only [v, hpure, hsize, and_false, ite_false, groupHarmonicTerm, hrpos,
        and_self, ite_true, Nat.cast_mul]
      simpa only [v, hp, mul_zero]
  · simp [hpure, groupHarmonicTerm]

theorem eventually_candidate_mass_harmonic (C : CandidateData) (δ : ℝ)
    (hC : C.Geometry δ) :
    ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ,
      C.mass x jstar =
        ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
          ∑ z : C.bands.Lists x jstar, (C.bands.listProduct z : ℝ)⁻¹ *
            ∑' r : ℕ,
              groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
                ((C.bands.listProduct z : ℝ) * r) *
                  C.psi (((C.bands.listProduct z : ℝ) * r) / x) := by
  rcases hC with ⟨hD, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hpsi, _, _⟩
  filter_upwards [eventually_listProduct_groupFree C.bands hD, eventually_gt_atTop 0]
    with x hx hx0
  exact fun jstar => candidate_mass_harmonic C hpsi x hx0 jstar (hx jstar)

end Erdos821.P7Core

