import Erdos821.P9.PairSieveData
import Erdos821.P9.PairGrid

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

private theorem natCast_zmod_zero_dvd (p n : ℕ) [NeZero p]
    (h : (n : ZMod p) = 0) : p ∣ n := by
  have hmod := (natCast_zmod_eq_iff_mod_eq_val p n 0).mp h
  exact Nat.dvd_of_mod_eq_zero (by simpa using hmod)

theorem pairSieveBad_false_of_rough
    (W : ℝ) (P A : Finset ℕ) (p m n u : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p)
    (hroughM : Analytic.rough W m) (hroughN : Analytic.rough W n)
    (hmn : m * n = 2 * u + 1)
    (hnoBanned : p ∉ P ∨ p ∉ A → ¬ p ∣ u) :
    ¬ pairSieveBad W P A p (m, n) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hone (hban : p ∉ P ∨ p ∉ A) :
      ((m : ZMod p) * (n : ZMod p)) ≠ 1 := by
    intro hEq
    have hmul : (2 : ZMod p) * (u : ZMod p) = 0 := by
      calc
        (2 : ZMod p) * (u : ZMod p) = ((2 * u : ℕ) : ZMod p) := by simp
        _ = ((2 * u + 1 : ℕ) : ZMod p) - 1 := by
          rw [Nat.cast_add]
          simp
        _ = ((m * n : ℕ) : ZMod p) - 1 := by rw [← hmn]
        _ = (m : ZMod p) * (n : ZMod p) - 1 := by rw [Nat.cast_mul]
        _ = 0 := by rw [hEq]; ring
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h2
      have hdiv : p ∣ 2 := natCast_zmod_zero_dvd p 2 h2
      have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
      omega
    have hu0 : (u : ZMod p) = 0 := (mul_eq_zero.mp hmul).resolve_left h2ne
    exact hnoBanned hban (natCast_zmod_zero_dvd p u hu0)
  intro hbad
  unfold pairSieveBad pairBadLocal at hbad
  by_cases hpW : (p : ℝ) ≤ W
  · have hprod0 : ((m : ZMod p) * (n : ZMod p)) ≠ 0 := by
      intro hz
      rcases mul_eq_zero.mp hz with hm0 | hn0
      · have hdiv := natCast_zmod_zero_dvd p m hm0
        exact (not_lt_of_ge hpW) (hroughM.2 p hp hdiv)
      · have hdiv := natCast_zmod_zero_dvd p n hn0
        exact (not_lt_of_ge hpW) (hroughN.2 p hp hdiv)
    by_cases hban : p ∉ P ∨ p ∉ A
    · simp [hpW, hban, hprod0, hone hban] at hbad
    · simp [hpW, hban, hprod0] at hbad
  · by_cases hban : p ∉ P ∨ p ∉ A
    · simp [hpW, hban, hone hban] at hbad
    · simp [hpW, hban] at hbad

theorem pairSieveData_object_and_good_of_conditions
    (a b c e D : ℕ) (W : ℝ) (P A Q : Finset ℕ)
    (hD : 0 < D) (hQprime : ∀ p ∈ Q, p.Prime)
    (hQlarge : ∀ p ∈ Q, 3 ≤ p)
    (m n u : ℕ) (hm : m ∈ Finset.Ico a b) (hn : n ∈ Finset.Ico c e)
    (hDdiv : D ∣ u) (hmn : m * n = 2 * u + 1)
    (hroughM : Analytic.rough W m) (hroughN : Analytic.rough W n)
    (hnoBanned : ∀ p ∈ Q, p ∉ P ∨ p ∉ A → ¬ p ∣ u) :
    let S := pairSieveData a b c e D W P A Q hD hQprime
    (m, n) ∈ S.objects ∧ ∀ p ∈ Q, ¬ S.bad p (m, n) := by
  classical
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  let hucast : (u : ZMod D) = 0 := by
    apply (natCast_zmod_eq_iff_mod_eq_val D u 0).2
    simpa using Nat.mod_eq_zero_of_dvd hDdiv
  have hbaseCast : (m : ZMod D) * (n : ZMod D) = 1 := by
    calc
      (m : ZMod D) * (n : ZMod D) = ((m * n : ℕ) : ZMod D) := by simp
      _ = ((2 * u + 1 : ℕ) : ZMod D) := by rw [hmn]
      _ = 1 := by rw [Nat.cast_add, Nat.cast_mul, hucast]; simp
  have hbase : pairSieveBaseGood D 1 (m, n) := by
    simpa [pairSieveBaseGood, pairBaseReduction_natCast] using hbaseCast
  let S := pairSieveData a b c e D W P A Q hD hQprime
  refine ⟨?_, ?_⟩
  · change (m, n) ∈
      (Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
        (pairSieveBaseGood D 1)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hm, hn⟩, hbase⟩
  · intro p hpQ
    have hp := hQprime p hpQ
    have hp3 := hQlarge p hpQ
    change ¬ pairSieveBad W P A p (m, n)
    exact pairSieveBad_false_of_rough W P A p m n u hp hp3 hroughM hroughN
      hmn (hnoBanned p hpQ)

theorem sieveData_sifted_eq_filtered_card
    {α : Type} (S : Erdos821.Blueprint.SieveData α)
    (hweight : ∀ z ∈ S.objects, S.weight z = 1) :
    S.sifted =
      ((S.objects.filter fun z => ∀ p ∈ S.primes, ¬ S.bad p z).card : ℝ) := by
  classical
  let good := S.objects.filter fun z => ∀ p ∈ S.primes, ¬ S.bad p z
  have hcard : good.card =
      ∑ z ∈ S.objects, if ∀ p ∈ S.primes, ¬ S.bad p z then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp [good, Finset.sum_filter]
  unfold Erdos821.Blueprint.SieveData.sifted
  calc
    _ = ∑ z ∈ S.objects, if ∀ p ∈ S.primes, ¬ S.bad p z then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hweight z hz]
    _ = (good.card : ℝ) := by exact_mod_cast hcard.symm
    _ = _ := by rfl

theorem sifted_count_upper_of_subset
    {α : Type} (S : Erdos821.Blueprint.SieveData α)
    (hweight : ∀ z ∈ S.objects, S.weight z = 1)
    (T : Finset α)
    (hT : T ⊆ S.objects.filter fun z => ∀ p ∈ S.primes, ¬ S.bad p z) :
    (T.card : ℝ) ≤ S.sifted := by
  rw [sieveData_sifted_eq_filtered_card S hweight]
  exact_mod_cast Finset.card_le_card hT

theorem sum_indicator_subset_le_sifted
    {α : Type} (S : Erdos821.Blueprint.SieveData α)
    (hweight : ∀ z ∈ S.objects, S.weight z = 1)
    (B T : Finset α) (c : ℝ) (hc : 0 ≤ c) (f : α → ℝ)
    (hterm : ∀ z ∈ B, f z = if z ∈ T then c else 0)
    (hT : T ⊆ S.objects.filter fun z => ∀ p ∈ S.primes, ¬ S.bad p z) :
    (∑ z ∈ B, f z) ≤ c * S.sifted := by
  let U := B.filter fun z => z ∈ T
  have hsum : (∑ z ∈ B, f z) = c * (U.card : ℝ) := by
    calc
      _ = ∑ z ∈ B, if z ∈ T then c else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hterm z hz
      _ = c * (U.card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [U, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hU : U ⊆ T := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hcard : (U.card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hU
  rw [hsum]
  calc
    c * (U.card : ℝ) ≤ c * (T.card : ℝ) := mul_le_mul_of_nonneg_left hcard hc
    _ ≤ c * S.sifted := mul_le_mul_of_nonneg_left
      (sifted_count_upper_of_subset S hweight T hT) hc


end

end Erdos821.P9Core
