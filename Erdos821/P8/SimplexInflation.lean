import Erdos821.P8.GridAbsorption

noncomputable section
open scoped BigOperators

namespace Erdos821.P8Core

/-- Enlarging a positive denominator incurs a controlled multiplicative kernel loss. -/
theorem inverse_kernel_inflation {b u v D eta V : ℝ}
    (hb : 0 < b) (hu : b / 2 ≤ u) (huv : u ≤ v)
    (hD : v - u ≤ D) (hV : v ≤ V) (heta : 0 ≤ eta) :
    u⁻¹ + eta ≤ (1 + 2 * D / b + eta * V) * v⁻¹ := by
  have hu0 : 0 < u := (by positivity : 0 < b / 2).trans_le hu
  have hv0 : 0 < v := hu0.trans_le huv
  have hdelta : 0 ≤ v - u := sub_nonneg.mpr huv
  have hInv : u⁻¹ ≤ 2 / b := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < b / 2) hu
    simpa only [one_div, inv_div] using h
  have hprod : u⁻¹ * (v - u) ≤ (2 / b) * D :=
    mul_le_mul hInv hD hdelta (by positivity)
  have hetaV := mul_le_mul_of_nonneg_left hV heta
  have hcancel : u⁻¹ * u = 1 := inv_mul_cancel₀ (ne_of_gt hu0)
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hv0).2
  have hEq : 2 * D / b = (2 / b) * D := by ring
  rw [hEq]
  nlinarith

/-- Rounding down an active exponent tuple puts its whole box in an inflated simplex. -/
theorem rounded_box_inside_inflated_simplex {α : Type*} [Fintype α]
    {gamma w d h : ℝ} {K : ℕ} (a e : α → ℝ)
    (hh : 0 ≤ h) (hk : Fintype.card α ≤ K)
    (hae : ∀ i, a i ≤ e i) (hea : ∀ i, e i ≤ a i + h)
    (hgamma : ∀ i, gamma ≤ e i) (hsum : (∑ i, e i) ≤ w + d - gamma) :
    (∀ i, gamma - h ≤ a i) ∧
      (∑ i, (a i + h)) ≤ w + d + ((K : ℝ) + 1) * h - (gamma - h) := by
  constructor
  · intro i
    linarith [hea i, hgamma i]
  · have hs : (∑ i, a i) ≤ ∑ i, e i := Finset.sum_le_sum fun i _ => hae i
    have hk' : (Fintype.card α : ℝ) ≤ K := by exact_mod_cast hk
    have hkh := mul_le_mul_of_nonneg_right hk' hh
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    nlinarith

/-- The last-prime kernel is bounded uniformly by the relaxed lower-corner kernel. -/
theorem rounded_box_kernel_inflation {α : Type*} [Fintype α]
    {b gamma w d h eta : ℝ} {K : ℕ} (a e : α → ℝ)
    (hb : 0 < b) (hbg : b ≤ gamma) (hd : 0 ≤ d) (hdb : d ≤ b / 2)
    (hh : 0 ≤ h) (hhb : h ≤ b / 2) (heta : 0 ≤ eta)
    (hk : Fintype.card α ≤ K) (hae : ∀ i, a i ≤ e i)
    (hea : ∀ i, e i ≤ a i + h) (hgamma : ∀ i, gamma ≤ e i)
    (hsum : (∑ i, e i) ≤ w + d - gamma) :
    (w - ∑ i, e i)⁻¹ + eta ≤
      (1 + 2 * (d + (2 * (K : ℝ) + 1) * h) / b +
        eta * (w + d + ((K : ℝ) + 1) * h)) *
      (w + d + ((K : ℝ) + 1) * h - ∑ i, a i)⁻¹ := by
  have hsumLE : (∑ i, a i) ≤ ∑ i, e i := Finset.sum_le_sum fun i _ => hae i
  have hsumUpper : (∑ i, e i) ≤ (∑ i, a i) + (Fintype.card α : ℝ) * h := by
    calc
      (∑ i, e i) ≤ ∑ i, (a i + h) := Finset.sum_le_sum fun i _ => hea i
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
  have hk' : (Fintype.card α : ℝ) ≤ K := by exact_mod_cast hk
  have hkh := mul_le_mul_of_nonneg_right hk' hh
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    linarith [hgamma i, hea i]
  have hsum0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha0 i
  apply inverse_kernel_inflation hb
  · linarith
  · have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith
  · linarith
  · linarith
  · exact heta

end Erdos821.P8Core

