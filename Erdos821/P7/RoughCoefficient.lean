import Erdos821.P6Slot.SlotMultiplicity
import Erdos821.S56.RoughDivisorBound

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic
open Erdos821.P6Slot

/-- The designated entry maps into the rough divisors of the product. The
accepted fixed-entry fiber bound retains the original factorial normalization. -/
theorem bandCoefficient_le_roughDivisors (D : BandData) (x : ℝ) (jstar v : ℕ)
    (hj : jstar ≤ D.last x) (hr : 0 < D.r₀)
    (hdisj : ∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j →
      Disjoint (D.band x i) (D.band x j)) :
    D.aQ x jstar v ≤ ((v.divisors.filter (rough (W x))).card : ℝ) := by
  classical
  let S : Finset (D.Lists x jstar) :=
    Finset.univ.filter (fun z => D.listProduct z = v)
  let e : D.Lists x jstar → ℕ := fun z => (z (exceptionSlot D x jstar hj hr)).val
  let R := v.divisors.filter (rough (W x))
  let F : ℕ := D.r₀.factorial ^ (D.last x + 1)
  have hmaps : ∀ z ∈ S, e z ∈ R := by
    intro z hz
    have hprod : D.listProduct z = v := (Finset.mem_filter.mp hz).2
    have hv : 0 < v := hprod ▸ list_product_pos D x jstar z
    have hediv : e z ∣ v := by
      refine ⟨pureProduct D x jstar hj hr z, ?_⟩
      simpa only [e, mul_comm] using
        hprod.symm.trans (listProduct_eq_pureProduct_mul D x jstar hj hr z)
    have hrough : rough (W x) (e z) := by
      have hmem := (z (exceptionSlot D x jstar hj hr)).property
      simp only [BandData.slotValues, exceptionSlot, and_self, ite_true] at hmem
      exact (Finset.mem_filter.mp hmem).2
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hediv, hv.ne'⟩, hrough⟩
  have hfibers : ∀ a ∈ R, (S.filter (fun z => e z = a)).card ≤ F := by
    intro a _
    have hcard : Fintype.card {z : D.Lists x jstar // D.listProduct z = v ∧ e z = a} =
        (S.filter (fun z => e z = a)).card := by
      apply Fintype.card_of_subtype
      intro z
      simp [S]
    rw [← hcard]
    exact list_fiber_card_le_factorial_pow D x jstar v a hj hr hdisj
  have hcount : S.card ≤ F * R.card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps F hfibers
  have hcountR : (S.card : ℝ) ≤ (D.r₀.factorial : ℝ) ^ (D.last x + 1) * R.card := by
    exact_mod_cast hcount
  have hF : (0 : ℝ) < (D.r₀.factorial : ℝ) ^ (D.last x + 1) := by positivity
  unfold BandData.aQ
  change ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ * (S.card : ℝ) ≤ _
  calc
    _ ≤ ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ *
        ((D.r₀.factorial : ℝ) ^ (D.last x + 1) * R.card) :=
      mul_le_mul_of_nonneg_left hcountR (by positivity)
    _ = (R.card : ℝ) := by rw [← mul_assoc, inv_mul_cancel₀ hF.ne', one_mul]

theorem bandCoefficient_exp_bound (D : BandData) (hD : D.Valid) :
    ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop, ∀ v : ℕ,
      0 < v → (v : ℝ) ≤ 5 * x → D.aQ x jstar v ≤ Real.exp (2 * Real.sqrt (L x)) := by
  intro jstar
  have hdata := hD
  obtain ⟨_, _, _, _, _, _, _, hlast, cmin, cmax, _, _, hevent⟩ := hdata
  filter_upwards [hlast.eventually_ge_atTop jstar, hevent,
    eventually_ge_atTop (5 : ℝ)] with x hj hx hlarge
  intro v hv hvx
  exact (bandCoefficient_le_roughDivisors D x jstar v hj
    (Nat.succ_le_iff.mp hD.1) hx.2.2.2.1).trans
    (Erdos821.S56Core.rough_divisor_exp_bound x hlarge v hv hvx)

end Erdos821.P7Core

