import Mathlib
import Erdos821.Challenge

/-!
# Fidelity bridge: Formal Conjectures' `erdos_821`

The namespace `Erdos821.Fidelity.FormalConjectures` restates, using Mathlib only, the
proposition of `Erdos821.erdos_821` from Google DeepMind's `formal-conjectures`, file
`FormalConjectures/ErdosProblems/821.lean` at commit
`317647fa3fc24ae900a50382186da1d22e4ea398` (last change to the file: `6fbb54f2`).
That file is Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License,
Version 2.0 (<https://www.apache.org/licenses/LICENSE-2.0>).

The definition `g` and the right-hand side of `erdos_821` are copied verbatim. The only change is
`answer(sorry)`, which Formal Conjectures' `answer()` elaborator turns into the proposition given as
the answer; with the answer `True` the statement reads `True ↔ …`.

The namespace `Erdos821.Fidelity.Source` restates the source paper's Theorem 1.1, which counts
only positive `m` and positive `n`, and Pomerance's exponent form "`g n > n ^ c` infinitely often for
every `c < 1`". Each is proved equivalent to `Erdos821.Statement`.
-/

namespace Erdos821.Fidelity

namespace FormalConjectures

open Nat Filter

/--
Let $g(n)$ count the number of $m$ such that $\phi(m)=n$.
-/
noncomputable def g (n : ℕ) : ℕ :=
  { m : ℕ | totient m = n }.ncard

/-- `erdos_821` of Formal Conjectures with `answer(True)`. -/
def erdos_821_answer_true : Prop :=
  True ↔ ∀ ε > (0 : ℝ), { n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε) }.Infinite

end FormalConjectures

/-- The project's `g` is Formal Conjectures' `g`. -/
theorem g_eq_formalConjectures_g : Erdos821.g = FormalConjectures.g := rfl

/-- The project target is Formal Conjectures' `erdos_821` with the answer `True`. -/
theorem statement_iff_formalConjectures :
    Erdos821.Statement ↔ FormalConjectures.erdos_821_answer_true :=
  ⟨fun h => iff_of_true trivial h, fun h => h.mp trivial⟩

namespace Source

/-- Every `m` with `φ m = n ≥ 1` lies in `[1, n * ∏_{p ≤ n + 1} p]` (the argument of OpenAI's
`OAI.TotientFibers.preimage_le`, Apache-2.0). -/
theorem fiber_bound {m n : ℕ} (hn : 1 ≤ n) (h : Nat.totient m = n) :
    1 ≤ m ∧ m ≤ n * ∏ p ∈ Finset.Icc 1 (n + 1), p := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h; omega
  refine ⟨hm, ?_⟩
  have hs : m.primeFactors ⊆ Finset.Icc 1 (n + 1) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hd : p - 1 ∣ n := by
      rw [← h, ← Nat.totient_prime hp']
      exact Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    have := Nat.le_of_dvd hn hd
    exact Finset.mem_Icc.mpr ⟨hp'.one_le, by omega⟩
  calc
    m ≤ m * ∏ p ∈ m.primeFactors, (p - 1) := by
      apply Nat.le_mul_of_pos_right
      exact Finset.prod_pos fun p hp => Nat.sub_pos_of_lt
        (Nat.prime_of_mem_primeFactors hp).one_lt
    _ = n * ∏ p ∈ m.primeFactors, p := by
      rw [← h, Nat.totient_mul_prod_primeFactors]
    _ ≤ n * ∏ p ∈ Finset.Icc 1 (n + 1), p := by
      apply Nat.mul_le_mul_left
      exact Finset.prod_le_prod_of_subset_of_one_le hs fun p hp _ =>
        (Finset.mem_Icc.mp hp).1

/-- Every fiber of `φ` is finite, so `Set.ncard` in `g` is its true cardinality (an infinite set
would have `ncard` zero). The fiber of `0` is `{0}`. -/
theorem totient_fiber_finite (n : ℕ) : {m : ℕ | Nat.totient m = n}.Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact (Set.finite_Icc 1 (n * ∏ p ∈ Finset.Icc 1 (n + 1), p)).subset fun m h => fiber_bound hn h

/-- `g n` is the cardinality of the finite fiber `{m | φ m = n}`. -/
theorem g_eq_card_toFinset (n : ℕ) :
    Erdos821.g n = (totient_fiber_finite n).toFinset.card :=
  Set.ncard_eq_toFinset_card _ _

/-- The source's `g(n) = #{m ≥ 1 : φ(m) = n}`. -/
noncomputable def g (n : ℕ) : ℕ :=
  {m : ℕ | 1 ≤ m ∧ Nat.totient m = n}.ncard

/-- Theorem 1.1 of the source: for every real `ε > 0` there are infinitely many positive integers
`n` with `g(n) > n ^ (1 - ε)`. -/
def Theorem_1_1 : Prop :=
  ∀ ε : ℝ, 0 < ε → {n : ℕ | 1 ≤ n ∧ (n : ℝ) ^ (1 - ε) < (g n : ℝ)}.Infinite

/-- Pomerance's formulation (`C = 1`, the lower half): for every exponent `c < 1`, `g(n) > n ^ c`
for infinitely many positive `n`. -/
def ExponentForm : Prop :=
  ∀ c : ℝ, c < 1 → {n : ℕ | 1 ≤ n ∧ (n : ℝ) ^ c < (g n : ℝ)}.Infinite

/-- For `n ≥ 1` the project's `g` agrees with the source's (only `m = 0` differs, and `φ 0 = 0`). -/
theorem g_eq_of_pos {n : ℕ} (hn : 1 ≤ n) : g n = Erdos821.g n := by
  unfold g Erdos821.g
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq, and_iff_right_iff_imp]
  intro h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at h; omega
  · exact hm

/-- At `n = 0` the two differ: `φ m = 0` only for `m = 0`, so the project's `g 0 = 1`. -/
theorem project_g_zero : Erdos821.g 0 = 1 := by
  simp [Erdos821.g, Nat.totient_eq_zero]

private theorem infinite_pos_iff (P : ℕ → Prop) :
    {n : ℕ | 1 ≤ n ∧ P n}.Infinite ↔ {n : ℕ | P n}.Infinite := by
  have hset : {n : ℕ | 1 ≤ n ∧ P n} = {n : ℕ | P n} \ {0} := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, by omega⟩, fun ⟨h1, h2⟩ => ⟨by omega, h1⟩⟩
  rw [hset]
  exact ⟨fun h => h.mono Set.sdiff_subset, fun h => h.sdiff (Set.finite_singleton 0)⟩

/-- The project target is the source's Theorem 1.1. -/
theorem statement_iff_theorem_1_1 : Erdos821.Statement ↔ Theorem_1_1 := by
  have key : ∀ ε : ℝ, {n : ℕ | 1 ≤ n ∧ (n : ℝ) ^ (1 - ε) < (g n : ℝ)} =
      {n : ℕ | 1 ≤ n ∧ (Erdos821.g n : ℝ) > (n : ℝ) ^ (1 - ε)} := by
    intro ε
    ext n
    simp only [Set.mem_ofPred_eq, gt_iff_lt]
    constructor
    · rintro ⟨hn, h⟩; exact ⟨hn, g_eq_of_pos hn ▸ h⟩
    · rintro ⟨hn, h⟩; exact ⟨hn, (g_eq_of_pos hn).symm ▸ h⟩
  unfold Erdos821.Statement Theorem_1_1
  refine forall_congr' fun ε => imp_congr_right fun _ => ?_
  rw [key, infinite_pos_iff (fun n => (Erdos821.g n : ℝ) > (n : ℝ) ^ (1 - ε))]

/-- The project target is the exponent form `∀ c < 1`. -/
theorem statement_iff_exponentForm : Erdos821.Statement ↔ ExponentForm := by
  rw [statement_iff_theorem_1_1]
  constructor
  · intro h c hc
    simpa using h (1 - c) (by linarith)
  · intro h ε hε
    exact h (1 - ε) (by linarith)

end Source

end Erdos821.Fidelity
