import Erdos821.P9.PairGrid
import Erdos821.P9.CRT

open scoped BigOperators
open Filter

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Counting pairs in a box after the fixed `D` congruence and squarefree local
bad events differs from its area term by the total lattice error. -/
theorem pair_grid_crt_remainder_bound
    (a b c e D d : ℕ) (W : ℝ) (P A : Finset ℕ)
    (hab : a ≤ b) (hce : c ≤ e) (hD : 0 < D) (hd : 0 < d)
    (hcop : Nat.Coprime D d) (hsq : Squarefree d)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p) [NeZero (D * d)] :
    let r := D * d
    let R : Finset (ZMod r × ZMod r) := Finset.univ.filter fun v =>
      pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧
        ∀ p : d.primeFactors,
          pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A))
            (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)
    |(((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
        fun z => pairResidue r z ∈ R).card : ℝ) -
      (Nat.totient D : ℝ) *
        (∏ p : d.primeFactors,
          pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ) *
        ((b - a : ℕ) : ℝ) * (e - c : ℕ) / (r : ℝ) ^ 2|
      ≤ (D : ℝ) * d ^ (2 : ℕ) *
        (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := by
  classical
  let r := D * d
  let R : Finset (ZMod r × ZMod r) := Finset.univ.filter fun v =>
    pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧
      ∀ p : d.primeFactors,
        pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A))
          (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  letI : NeZero r := ⟨Nat.ne_of_gt (Nat.mul_pos hD hd)⟩
  letI : ∀ p : d.primeFactors, NeZero p.val := fun p =>
    ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  have hr : 0 < r := Nat.mul_pos hD hd
  have hrootCard : R.card = Nat.totient D *
      ∏ p : d.primeFactors,
        pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) := by
    simpa [R, r, Fintype.card_subtype] using
      pair_crt_divisibility_root_count D d W P A hcop (Nat.ne_of_gt hD)
        (Nat.ne_of_gt hd) hsq hd3
  have hrootCardLe : R.card ≤ D * d ^ (2 : ℕ) := by
    simpa [R, r, Fintype.card_subtype] using
      pair_crt_divisibility_root_count_le D d W P A hcop
        (Nat.ne_of_gt hD) (Nat.ne_of_gt hd) hsq hd3
  have hgrid := pair_grid_count_area_error a b c e r hab hce hr R
  have hrootCardR : (R.card : ℝ) = (Nat.totient D : ℝ) *
      (∏ p : d.primeFactors,
        (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) := by
    exact_mod_cast hrootCard
  have hmain : (R.card : ℝ) * ((b - a : ℕ) : ℝ) * (e - c : ℕ) /
        (r : ℝ) ^ 2 =
      (Nat.totient D : ℝ) *
        (∏ p : d.primeFactors,
          (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) *
        ((b - a : ℕ) : ℝ) * (e - c : ℕ) / (r : ℝ) ^ 2 := by
    rw [hrootCardR]
  have hgrid' :
      |(((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
          fun z => pairResidue r z ∈ R).card : ℝ) -
        (Nat.totient D : ℝ) *
          (∏ p : d.primeFactors,
            (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
              (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) *
          ((b - a : ℕ) : ℝ) * (e - c : ℕ) / (r : ℝ) ^ 2| ≤
        (R.card : ℝ) *
          (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := by
    rw [← hmain]
    exact hgrid
  have hcountLe : (R.card : ℝ) ≤ (D : ℝ) * (d : ℝ) ^ 2 := by
    exact_mod_cast hrootCardLe
  have herrNonneg : 0 ≤
      4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ) := by
    positivity
  calc
    |(((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
        fun z => pairResidue r z ∈ R).card : ℝ) -
      (Nat.totient D : ℝ) *
        (∏ p : d.primeFactors,
          (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) *
        ((b - a : ℕ) : ℝ) * (e - c : ℕ) / (r : ℝ) ^ 2| ≤
      (R.card : ℝ) *
        (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := hgrid'
    _ ≤ (D : ℝ) * (d : ℝ) ^ 2 *
        (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) :=
      mul_le_mul_of_nonneg_right hcountLe herrNonneg
    _ = _ := by rfl

theorem sum_nat_cast_Icc_le_square (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, (d : ℝ)) ≤ (n : ℝ) ^ 2 := by
  classical
  let s := Finset.Icc 1 n
  have hcard : s.card = n := by simp [s]
  have hsum : (∑ d ∈ s, (d : ℝ)) ≤ ∑ d ∈ s, (n : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    have hdle : d ≤ n := (Finset.mem_Icc.mp (by simpa [s] using hd)).2
    exact_mod_cast hdle
  calc
    (∑ d ∈ Finset.Icc 1 n, (d : ℝ)) = ∑ d ∈ s, (d : ℝ) := by rfl
    _ ≤ ∑ d ∈ s, (n : ℝ) := hsum
    _ = (n : ℝ) ^ 2 := by simp [Finset.sum_const, s, hcard]; ring

theorem sum_nat_cast_sq_Icc_le_cube (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, (d : ℝ) ^ 2) ≤ (n : ℝ) ^ 3 := by
  classical
  let s := Finset.Icc 1 n
  have hcard : s.card = n := by simp [s]
  have hsum : (∑ d ∈ s, (d : ℝ) ^ 2) ≤ ∑ d ∈ s, (n : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro d hd
    have hdmem : d ∈ Finset.Icc 1 n := by simpa [s] using hd
    have hleNat := (Finset.mem_Icc.mp hdmem).2
    have hle : (d : ℝ) ≤ n := by exact_mod_cast hleNat
    have hnonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc
    (∑ d ∈ Finset.Icc 1 n, (d : ℝ) ^ 2) = ∑ d ∈ s, (d : ℝ) ^ 2 := by rfl
    _ ≤ ∑ d ∈ s, (n : ℝ) ^ 2 := hsum
    _ = (n : ℝ) ^ 3 := by simp [Finset.sum_const, s, hcard]; ring

theorem sum_remainder_errors_level_bound
    (N : ℕ) (D W : ℝ) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N) (f : ℕ → ℝ)
    (hf : ∀ d ∈ S, |f d| ≤ 4 * D * (d : ℝ) ^ 2 + 2 * W * d) :
    (∑ d ∈ S, |f d|) ≤ 4 * D * (N : ℝ) ^ 3 + 2 * W * (N : ℝ) ^ 2 := by
  classical
  calc
    (∑ d ∈ S, |f d|) ≤
        ∑ d ∈ S, (4 * D * (d : ℝ) ^ 2 + 2 * W * d) :=
      Finset.sum_le_sum hf
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        (4 * D * (d : ℝ) ^ 2 + 2 * W * d) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (by
        intro d hd hnot
        positivity)
    _ = 4 * D * (∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ 2) +
          2 * W * (∑ d ∈ Finset.Icc 1 N, (d : ℝ)) := by
      calc
        _ = ∑ d ∈ Finset.Icc 1 N,
              (4 * D * (d : ℝ) ^ 2 + 2 * W * (d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 4 * D * (N : ℝ) ^ 3 + 2 * W * (N : ℝ) ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sum_nat_cast_sq_Icc_le_cube N) (by positivity)
      · exact mul_le_mul_of_nonneg_left (sum_nat_cast_Icc_le_square N) (by positivity)




end

end Erdos821.P9Core
