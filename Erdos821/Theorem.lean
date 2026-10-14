import Erdos821.Final.Assembly

/-!
# Erdős Problem 821

Let `g n` be the number of natural numbers `m` with `φ m = n`. For every `ε > 0`, infinitely many `n`
satisfy `g n > n ^ (1 - ε)`. This is Formal Conjectures' `Erdos821.erdos_821` with the answer `True`,
and Theorem 1.1 of OpenAI's paper *Weighted dilation graphs, smooth shifted primes and totient fibers*.

`Erdos821.Final.statement` proves `Erdos821.Statement` (`Erdos821/Challenge.lean`), whose body is the
proposition below.
-/

namespace Erdos821

/-- Erdős Problem 821: for every `ε > 0`, infinitely many `n` have more than `n ^ (1 - ε)` totient
preimages. -/
theorem erdos_821 :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite :=
  Final.statement

end Erdos821
