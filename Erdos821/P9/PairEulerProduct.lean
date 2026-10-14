import Erdos821.P9.EulerProduct
import Erdos821.Blueprint.Classical

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section

open Erdos821.Blueprint

theorem mem_primesUpTo_iff (y : ℝ) (hy : 0 ≤ y) (p : ℕ) :
    p ∈ primesUpTo y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp1, hpfloor⟩, hp⟩
    refine ⟨hp, ?_⟩
    have hcast : (p : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hpfloor
    exact le_trans hcast (Nat.floor_le hy)
  · rintro ⟨hp, hpy⟩
    refine ⟨⟨hp.one_le, (Nat.le_floor_iff hy).2 hpy⟩, hp⟩

theorem primesUpTo_mono {y z : ℝ} (hyz : y ≤ z) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    primesUpTo y ⊆ primesUpTo z := by
  intro p hp
  have hpy := (mem_primesUpTo_iff y hy p).1 hp
  exact (mem_primesUpTo_iff z hz p).2 ⟨hpy.1, hpy.2.trans hyz⟩

theorem pair_base_product_eq (W z : ℝ) (hW2 : 2 ≤ W) (hWz : W ≤ z) :
    (∏ p ∈ primesUpTo z, pairBaseFactor p W) =
      sieveProduct W ^ 2 * sieveProduct z := by
  classical
  let Q := primesUpTo z
  let QW := primesUpTo W
  have hW0 : 0 ≤ W := by linarith
  have hz0 : 0 ≤ z := le_trans (by linarith : (0 : ℝ) ≤ W) hWz
  have hsub : QW ⊆ Q := primesUpTo_mono hWz hW0 hz0
  have hlargeBase : ∀ p ∈ (Q \ QW), pairBaseFactor p W = 1 - 1 / (p : ℝ) := by
    intro p hp
    have hpQ : p ∈ Q := (Finset.mem_sdiff.mp hp).1
    have hpnotQW : p ∉ QW := (Finset.mem_sdiff.mp hp).2
    have hprime : p.Prime := (mem_primesUpTo_iff z hz0 p).1 hpQ |>.1
    have hpW : ¬ (p : ℝ) ≤ W := by
      intro h
      exact hpnotQW ((mem_primesUpTo_iff W hW0 p).2 ⟨hprime, h⟩)
    simp [pairBaseFactor, hpW]
  have hsmallBase : ∀ p ∈ QW, pairBaseFactor p W = (1 - 1 / (p : ℝ)) ^ 3 := by
    intro p hp
    have hpW : (p : ℝ) ≤ W := (mem_primesUpTo_iff W hW0 p).1 hp |>.2
    simp [pairBaseFactor, hpW]
  have hsplit :
      (∏ p ∈ Q, pairBaseFactor p W) =
        (∏ p ∈ (Q \ QW), (1 - 1 / (p : ℝ))) *
          (∏ p ∈ QW, (1 - 1 / (p : ℝ)) ^ 3) := by
    rw [← Finset.prod_sdiff hsub]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      exact hlargeBase p hp
    · apply Finset.prod_congr rfl
      intro p hp
      exact hsmallBase p hp
  have hparts :
      (∏ p ∈ Q, (1 - 1 / (p : ℝ))) =
        (∏ p ∈ QW, (1 - 1 / (p : ℝ))) *
          (∏ p ∈ (Q \ QW), (1 - 1 / (p : ℝ))) := by
    calc
      (∏ p ∈ Q, (1 - 1 / (p : ℝ))) =
          (∏ p ∈ (Q \ QW), (1 - 1 / (p : ℝ))) *
            (∏ p ∈ QW, (1 - 1 / (p : ℝ))) := (Finset.prod_sdiff hsub).symm
      _ = (∏ p ∈ QW, (1 - 1 / (p : ℝ))) *
            (∏ p ∈ (Q \ QW), (1 - 1 / (p : ℝ))) := by ac_rfl
  have hVparts : sieveProduct z =
      sieveProduct W * (∏ p ∈ (Q \ QW), (1 - 1 / (p : ℝ))) := by
    simpa [sieveProduct, Q, QW, one_div] using hparts
  have hpow : (∏ p ∈ QW, (1 - 1 / (p : ℝ)) ^ 3) = sieveProduct W ^ 3 := by
    simp [sieveProduct, QW, Finset.prod_pow]
  rw [hsplit, hpow, hVparts]
  ring

theorem pair_sieve_product_bound (W z : ℝ) (D : ℕ) (P A : Finset ℕ)
    (hW2 : 2 ≤ W) (hWz : W ≤ z) (hP : P ⊆ primesUpTo W) (hA : A ⊆ P) :
    pairFiniteProduct (primesUpTo z) W D P A ≤
      8 * Real.exp 2 * sieveProduct W ^ 2 * sieveProduct z *
        (∏ p ∈ primesUpTo z, pairDComp p D) *
          (∏ p ∈ primesUpTo z, pairAComp p D A) := by
  classical
  let Q := primesUpTo z
  let QW := primesUpTo W
  have hW0 : 0 ≤ W := by linarith
  have hz0 : 0 ≤ z := le_trans hW0 hWz
  have hQ2 : 2 ∈ Q := by
    have h2z : (2 : ℝ) ≤ z := le_trans hW2 hWz
    exact (mem_primesUpTo_iff z hz0 2).2 ⟨Nat.prime_two, h2z⟩
  have hQprime : ∀ p ∈ Q, p.Prime := by
    intro p hp
    exact (mem_primesUpTo_iff z hz0 p).1 hp |>.1
  have hQWle : ∀ p ∈ QW, (p : ℝ) ≤ W := by
    intro p hp
    exact (mem_primesUpTo_iff W hW0 p).1 hp |>.2
  have hQsmall : Q.filter (fun p => 3 ≤ p) ⊆ Finset.Icc 3 ⌊z⌋₊ := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpz : (p : ℝ) ≤ z := (mem_primesUpTo_iff z hz0 p).1 hp'.1 |>.2
    exact Finset.mem_Icc.mpr ⟨hp'.2, (Nat.le_floor_iff hz0).2 hpz⟩
  have hfinite := pair_finite_product_bound Q QW P A W D ⌊z⌋₊
    hW2 hQ2 hQprime hQWle hP hA hQsmall
  have hfinite' := hfinite
  rw [pair_base_product_eq W z hW2 hWz] at hfinite'
  calc
    pairFiniteProduct (primesUpTo z) W D P A ≤
        8 * Real.exp 2 * (sieveProduct W ^ 2 * sieveProduct z) *
          (∏ p ∈ primesUpTo z, pairDComp p D) *
            (∏ p ∈ primesUpTo z, pairAComp p D A) := by
      simpa [Q, QW] using hfinite'
    _ =
        8 * Real.exp 2 * sieveProduct W ^ 2 * sieveProduct z *
          (∏ p ∈ primesUpTo z, pairDComp p D) *
            (∏ p ∈ primesUpTo z, pairAComp p D A) := by ring


end

end Erdos821.P9Core
