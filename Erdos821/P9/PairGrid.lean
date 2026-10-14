import Erdos821.P9.Lattice

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Reduction of a natural pair to its two residue coordinates. -/
def pairResidue (r : ℕ) (z : ℕ × ℕ) : ZMod r × ZMod r :=
  ((z.1 : ZMod r), (z.2 : ZMod r))

theorem natCast_zmod_eq_iff_mod_eq_val (r n : ℕ) [NeZero r] (q : ZMod r) :
    (n : ZMod r) = q ↔ n % r = q.val := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt n hr)] using hv
  · intro h
    apply ZMod.val_injective r
    have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt n hr)] using h

theorem pair_grid_residue_fiber_count
    (a b c d r : ℕ) (hr : 0 < r) (R : Finset (ZMod r × ZMod r)) :
    (Finset.product (Finset.Ico a b) (Finset.Ico c d) |>.filter
      fun z => pairResidue r z ∈ R).card =
      ∑ q ∈ R,
        ((Finset.Ico a b).filter fun m => m % r = q.1.val).card *
          ((Finset.Ico c d).filter fun n => n % r = q.2.val).card := by
  classical
  letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  let grid := Finset.product (Finset.Ico a b) (Finset.Ico c d)
  let valid := grid.filter fun z => pairResidue r z ∈ R
  have hcard : valid.card =
      ∑ q ∈ R, (valid.filter fun z => pairResidue r z = q).card := by
    simpa [valid] using
      (Finset.card_eq_sum_card_fiberwise
        (f := pairResidue r) (s := valid) (t := R)
        (fun z hz => (Finset.mem_filter.mp hz).2))
  have hfiber (q : ZMod r × ZMod r) (hq : q ∈ R) :
      valid.filter (fun z => pairResidue r z = q) =
        (Finset.Ico a b).filter (fun m => m % r = q.1.val) ×ˢ
          (Finset.Ico c d).filter (fun n => n % r = q.2.val) := by
    ext z
    rcases z with ⟨m, n⟩
    constructor
    · intro hz
      rcases Finset.mem_filter.mp hz with ⟨hzvalid, heq⟩
      rcases Finset.mem_filter.mp hzvalid with ⟨hzgrid, hR⟩
      rcases Finset.mem_product.mp hzgrid with ⟨hm, hn⟩
      have h₁ := (natCast_zmod_eq_iff_mod_eq_val r m q.1).mp
        (congrArg Prod.fst heq)
      have h₂ := (natCast_zmod_eq_iff_mod_eq_val r n q.2).mp
        (congrArg Prod.snd heq)
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hm, h₁⟩,
        Finset.mem_filter.mpr ⟨hn, h₂⟩⟩
    · intro hz
      rcases Finset.mem_product.mp hz with ⟨hm, hn⟩
      rcases Finset.mem_filter.mp hm with ⟨hmgrid, hmodm⟩
      rcases Finset.mem_filter.mp hn with ⟨hngrid, hmodn⟩
      have heq : pairResidue r (m, n) = q := by
        apply Prod.ext
        · exact (natCast_zmod_eq_iff_mod_eq_val r m q.1).mpr hmodm
        · exact (natCast_zmod_eq_iff_mod_eq_val r n q.2).mpr hmodn
      have hR : pairResidue r (m, n) ∈ R := heq ▸ hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hmgrid, hngrid⟩, hR⟩, heq⟩

  rw [hcard]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hfiber q hq, Finset.card_product]

theorem pair_grid_count_area_error
    (a b c d r : ℕ) (hab : a ≤ b) (hcd : c ≤ d) (hr : 0 < r)
    (R : Finset (ZMod r × ZMod r)) :
    |(((Finset.product (Finset.Ico a b) (Finset.Ico c d)).filter
        fun z => pairResidue r z ∈ R).card : ℝ) -
      (R.card : ℝ) * ((b - a : ℕ) : ℝ) * (d - c : ℕ) / (r : ℝ) ^ 2| ≤
      (R.card : ℝ) *
        (4 + 2 * (((b - a : ℕ) : ℝ) + (d - c : ℕ)) / (r : ℝ)) := by
  classical
  letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  let grid := Finset.product (Finset.Ico a b) (Finset.Ico c d)
  let valid := grid.filter fun z => pairResidue r z ∈ R
  let F := fun q : ZMod r × ZMod r =>
    (((Finset.Ico a b).filter fun m => m % r = q.1.val).card : ℝ) *
      ((Finset.Ico c d).filter fun n => n % r = q.2.val).card
  let area : ℝ := ((b - a : ℕ) : ℝ) * (d - c : ℕ) / (r : ℝ) ^ 2
  let err : ℝ := 4 + 2 * (((b - a : ℕ) : ℝ) + (d - c : ℕ)) / (r : ℝ)
  have hcount := pair_grid_residue_fiber_count a b c d r hr R
  have hcountR : (valid.card : ℝ) = ∑ q ∈ R, F q := by
    dsimp [valid, grid, F]
    exact_mod_cast hcount
  have hlocal : ∀ q ∈ R, |F q - area| ≤ err := by
    intro q hq
    have hlat := pair_lattice_count_nat a b c d r q.1.val q.2.val hab hcd hr
    simpa [F, area, err, Nat.mod_eq_of_lt q.1.val_lt,
      Nat.mod_eq_of_lt q.2.val_lt] using hlat
  have hmain : (valid.card : ℝ) - (R.card : ℝ) * area =
      ∑ q ∈ R, (F q - area) := by
    rw [hcountR, Finset.sum_sub_distrib]
    simp [area, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have herror : |(valid.card : ℝ) - (R.card : ℝ) * area| ≤
      (R.card : ℝ) * err := by
    calc
      |(valid.card : ℝ) - (R.card : ℝ) * area| =
          |∑ q ∈ R, (F q - area)| := by rw [hmain]
      _ ≤ ∑ q ∈ R, |F q - area| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ R, err := Finset.sum_le_sum (by
        intro q hq
        exact hlocal q hq)
      _ = (R.card : ℝ) * err := by simp [Finset.sum_const, nsmul_eq_mul]
  have hEq :
      (((Finset.product (Finset.Ico a b) (Finset.Ico c d)).filter
        fun z => pairResidue r z ∈ R).card : ℝ) -
        (R.card : ℝ) * ((b - a : ℕ) : ℝ) * (d - c : ℕ) / (r : ℝ) ^ 2 =
      (valid.card : ℝ) - (R.card : ℝ) * area := by
    simp [valid, grid, area]
    <;> ring
  calc
    |(((Finset.product (Finset.Ico a b) (Finset.Ico c d)).filter
        fun z => pairResidue r z ∈ R).card : ℝ) -
        (R.card : ℝ) * ((b - a : ℕ) : ℝ) * (d - c : ℕ) / (r : ℝ) ^ 2| =
      |(valid.card : ℝ) - (R.card : ℝ) * area| := by rw [hEq]
    _ ≤ (R.card : ℝ) * err := herror
    _ = (R.card : ℝ) *
        (4 + 2 * (((b - a : ℕ) : ℝ) + (d - c : ℕ)) / (r : ℝ)) := by rfl


end

end Erdos821.P9Core
