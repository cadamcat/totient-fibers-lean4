import Erdos821.P6Off.Task
import Erdos821.S56.DeterminantExistence
import Erdos821.S56.DeterminantConverse
import Erdos821.S56.CharacterCongruence

noncomputable section
open scoped BigOperators

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Turn the exact natural quotient used in offDiagonalSum back into its
factor equation. The strict lower bound protects natural subtraction. -/
theorem quotient_factor_equation (e m n : ℕ) (hlarge : 1 < m * n)
    (hdiv : 2 * e ∣ m * n - 1) :
    m * n = 2 * e * ((m * n - 1) / (2 * e)) + 1 := by
  rw [Nat.mul_div_cancel' hdiv]
  omega

/-- The h index in a nonzero off-diagonal term is positive. -/
theorem quotient_factor_pos (e m n : ℕ) (he : 0 < e) (hlarge : 1 < m * n)
    (hdiv : 2 * e ∣ m * n - 1) : 0 < (m * n - 1) / (2 * e) := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (by omega) hdiv
  · omega

/-- Signed determinant extracted from precisely the guards in offDiagonalSum.
No congruence or divisibility is inferred from truncated subtraction. -/
theorem offDiagonal_determinant (e n m m' : ℕ) (he : 0 < e)
    (hne : m ≠ m') (hm : 1 < m * n) (hm' : 1 < m' * n)
    (hd : 2 * e ∣ m * n - 1) (hd' : 2 * e ∣ m' * n - 1) :
    ∃ k : ℤ, k ≠ 0 ∧ (m' : ℤ) - m = 2 * e * k ∧
      (((m' * n - 1) / (2 * e) : ℕ) : ℤ) -
        ((m * n - 1) / (2 * e) : ℕ) = k * n ∧
      (m : ℤ) * ((m' * n - 1) / (2 * e) : ℕ) -
        (m' : ℤ) * ((m * n - 1) / (2 * e) : ℕ) = k := by
  apply Erdos821.S56.determinant_shift_exists
  · exact_mod_cast he
  · exact_mod_cast quotient_factor_equation e m n hm hd
  · exact_mod_cast quotient_factor_equation e m' n hm' hd'
  · exact_mod_cast hne

/-- Coprimality used by the converse, expressed for the literal blueprint roughness. -/
theorem rough_coprime_natAbs (y : ℝ) (m : ℕ) (k : ℤ) (hm : rough y m)
    (hk : k ≠ 0) (hsmall : (k.natAbs : ℝ) ≤ y) : Nat.Coprime m k.natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpk
  have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  have hle : (p : ℝ) ≤ k.natAbs := by exact_mod_cast Nat.le_of_dvd hkpos hpk
  exact (not_lt_of_ge (hle.trans hsmall)) (hm.2 p hp hpm)

/-- Positive natural reconstruction from the signed determinant. -/
theorem determinant_converse_nat (m m' e h h' : ℕ) (k : ℤ)
    (hm : 0 < m) (he : 0 < e) (hh : 0 < h)
    (hdelta : (m' : ℤ) - m = 2 * e * k)
    (hcross : (m : ℤ) * h' - (m' : ℤ) * h = k)
    (hcop : Nat.Coprime m k.natAbs) :
    ∃! n : ℕ, 0 < n ∧ m * n = 2 * e * h + 1 ∧
      m' * n = 2 * e * h' + 1 := by
  have hcop' : IsCoprime (m : ℤ) k := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact hcop
  obtain ⟨n, hn, huniq⟩ := Erdos821.S56.determinant_converse_unique
    m m' e h h' k (by exact_mod_cast hm) (by exact_mod_cast he)
    (by exact_mod_cast hh) hdelta hcross hcop'
  refine ⟨n.toNat, ?_, ?_⟩
  · have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.1.le
    refine ⟨by omega, ?_, ?_⟩
    · exact_mod_cast (show (m : ℤ) * n.toNat = 2 * e * h + 1 by rw [hcast]; exact hn.2.1)
    · exact_mod_cast (show (m' : ℤ) * n.toNat = 2 * e * h' + 1 by rw [hcast]; exact hn.2.2)
  · intro n' hn'
    have heq : (n' : ℤ) = n := huniq n'
      ⟨by exact_mod_cast hn'.1, by exact_mod_cast hn'.2.1, by exact_mod_cast hn'.2.2⟩
    exact_mod_cast heq.trans (Int.toNat_of_nonneg hn.1.le).symm


end Erdos821.P6Off
