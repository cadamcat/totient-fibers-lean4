import Mathlib

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section

/-- The two local bad events for the product of two variables. -/
theorem pair_bad_residue_counts (p : ℕ) [NeZero p] (hp : p.Prime) :
    (Finset.univ.filter (fun v : ZMod p × ZMod p => v.1 * v.2 = 0)).card = 2 * p - 1 ∧
    (Finset.univ.filter (fun v : ZMod p × ZMod p => v.1 * v.2 = 1)).card = p - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let leftAxis : Finset (ZMod p × ZMod p) := Finset.univ.image fun y => (0, y)
  let rightAxis : Finset (ZMod p × ZMod p) := Finset.univ.image fun x => (x, 0)
  have hleft : leftAxis.card = p := by
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      exact congrArg Prod.snd hab)]
    simp [ZMod.card]
  have hright : rightAxis.card = p := by
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      exact congrArg Prod.fst hab)]
    simp [ZMod.card]
  have hzero : Finset.univ.filter (fun v : ZMod p × ZMod p => v.1 * v.2 = 0) =
      leftAxis ∪ rightAxis := by
    ext v
    rcases v with ⟨x, y⟩
    simp [leftAxis, rightAxis, mul_eq_zero, eq_comm]
  have hinter : leftAxis ∩ rightAxis = {(0, 0)} := by
    ext v
    rcases v with ⟨x, y⟩
    simp [leftAxis, rightAxis, Prod.mk.injEq, and_comm, eq_comm]
  have hzeroCard : (Finset.univ.filter (fun v : ZMod p × ZMod p => v.1 * v.2 = 0)).card = 2 * p - 1 := by
    have hcard := Finset.card_union_add_card_inter leftAxis rightAxis
    rw [hleft, hright, hinter, Finset.card_singleton] at hcard
    rw [hzero]
    omega
  let unitGraph : Finset (ZMod p × ZMod p) :=
    Finset.univ.image fun u : (ZMod p)ˣ => ((u : ZMod p), ((u⁻¹ : (ZMod p)ˣ) : ZMod p))
  have hone : Finset.univ.filter (fun v : ZMod p × ZMod p => v.1 * v.2 = 1) = unitGraph := by
    ext v
    constructor
    · intro hv
      have hxy := (Finset.mem_filter.mp hv).2
      exact Finset.mem_image.mpr ⟨Units.mkOfMulEqOne v.1 v.2 hxy, Finset.mem_univ _, by cases v; rfl⟩
    · intro hv
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.val_inv⟩
  have hgraph : unitGraph.card = p - 1 := by
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      apply Units.ext
      exact congrArg Prod.fst hab)]
    rw [Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  exact ⟨hzeroCard, by rw [hone, hgraph]⟩

def pairNu (p : ℕ) (belowW banned : Bool) : ℝ :=
  (if belowW then 2 * (p : ℝ) - 1 else 0) +
    (if banned then (p : ℝ) - 1 else 0)

def pairDensity (p : ℕ) (belowW banned : Bool) : ℝ :=
  (pairNu p belowW banned : ℝ) / (p : ℝ) ^ 2

theorem pair_density_bound (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (a b : Bool) :
    0 ≤ pairDensity p a b ∧ pairDensity p a b ≤ 3 / (p : ℝ) ∧
      pairDensity p a b ≤ 7 / 9 := by
  have hp0 : 0 < p := hp.pos
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp0
  have hpR3 : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hprod : 0 ≤ ((p : ℝ) - 3) * (7 * p - 6) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hnu : 0 ≤ pairNu p a b := by
    cases a <;> cases b <;> simp [pairNu] <;> linarith
  have hupper : pairNu p a b ≤ 3 * p := by
    cases a <;> cases b <;> simp [pairNu] <;> linarith
  have hsmall : pairNu p a b ≤ (7 / 9 : ℝ) * p ^ 2 := by
    cases a <;> cases b <;> simp [pairNu] <;> nlinarith [hprod]
  constructor
  · exact div_nonneg hnu (sq_nonneg _)
  constructor
  · have h := div_le_div_of_nonneg_right hupper (sq_nonneg (p : ℝ))
    calc
      pairNu p a b / (p : ℝ) ^ 2 ≤ (3 * p) / (p : ℝ) ^ 2 := h
      _ = 3 / (p : ℝ) := by field_simp [ne_of_gt hpR]
  · have h' : (pairNu p a b : ℝ) / (p : ℝ) ^ 2 ≤ (7 / 9 : ℝ) := by
      calc
        pairNu p a b / (p : ℝ) ^ 2 ≤ ((7 / 9 : ℝ) * p ^ 2) / (p : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hsmall (sq_nonneg (p : ℝ))
        _ = 7 / 9 := by field_simp [ne_of_gt hpR]
    simpa [pairDensity] using h'

theorem mask_factor (p : ℕ) (hp : p.Prime) (q : ℝ) :
    1 - q + q / (1 - 1 / (p : ℝ)) = 1 + q / ((p : ℝ) - 1) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpR1 : (p : ℝ) - 1 ≠ 0 := by
    have hp2 : 2 ≤ p := hp.two_le
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt (by omega : 1 < p)))
  field_simp [hpR, hpR1]
  <;> ring

theorem banned_factor_bound (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    1 - pairDensity p true true ≤ (1 - 1 / (p : ℝ)) ^ 3 ∧
      1 - pairDensity p false true ≤
        (1 - 1 / (p : ℝ)) * (1 + 2 / (p : ℝ) ^ 2) := by
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  constructor
  · have h : pairDensity p true true = (3 * p - 2) / (p : ℝ) ^ 2 := by
      simp [pairDensity, pairNu]
      <;> ring
    rw [h]
    have hineq : 1 - (3 * (p : ℝ) - 2) / (p : ℝ) ^ 2 ≤
        (1 - 1 / (p : ℝ)) ^ 3 := by
      have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      have hp1 : (p : ℝ) ≠ 0 := ne_of_gt hpR
      field_simp [hp1]
      nlinarith [hp3R]
    exact hineq
  · have h : pairDensity p false true = ((p : ℝ) - 1) / (p : ℝ) ^ 2 := by
      simp [pairDensity, pairNu]
      <;> ring
    rw [h]
    have hineq : 1 - ((p : ℝ) - 1) / (p : ℝ) ^ 2 ≤
        (1 - 1 / (p : ℝ)) * (1 + 2 / (p : ℝ) ^ 2) := by
      have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      have hp1 : (p : ℝ) ≠ 0 := ne_of_gt hpR
      field_simp [hp1]
      nlinarith [hp3R]
    exact hineq


end

end Erdos821.P9Core
