import Erdos821.P9.PairSieve

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section

def pairLocalFactor (p : ℕ) (W : ℝ) (D : ℕ) (P A : Finset ℕ) : ℝ :=
  if 3 ≤ p ∧ ¬ p ∣ D then
    1 - pairDensity p (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))
  else 1

def pairBaseFactor (p : ℕ) (W : ℝ) : ℝ :=
  if (p : ℝ) ≤ W then (1 - 1 / (p : ℝ)) ^ 3 else 1 - 1 / (p : ℝ)

def pairDComp (p : ℕ) (D : ℕ) : ℝ :=
  if p ∣ D then ((1 - 1 / (p : ℝ)) ^ (3 : ℕ))⁻¹ else 1

def pairAComp (p : ℕ) (D : ℕ) (A : Finset ℕ) : ℝ :=
  if p ∈ A ∧ ¬ p ∣ D then (1 - 1 / (p : ℝ))⁻¹ else 1

def pairTailFactor (p : ℕ) (W : ℝ) : ℝ :=
  if W < (p : ℝ) then 1 + 2 / (p : ℝ) ^ 2 else 1

def pairConstantFactor (p : ℕ) : ℝ := if p = 2 then 8 else 1

theorem pairDensity_true_false (p : ℕ) (hp : p.Prime) :
    pairDensity p true false = (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2 := by
  simp [pairDensity, pairNu]

theorem pairDensity_false_true (p : ℕ) (hp : p.Prime) :
    pairDensity p false true = ((p : ℝ) - 1) / (p : ℝ) ^ 2 := by
  simp [pairDensity, pairNu]

theorem pair_local_factor_bound (p : ℕ) (W : ℝ) (D : ℕ) (QW P A : Finset ℕ)
    (hp : p.Prime) (hW2 : 2 ≤ W)
    (hQWle : ∀ q ∈ QW, (q : ℝ) ≤ W) (hP : P ⊆ QW) (hA : A ⊆ P) :
    pairLocalFactor p W D P A ≤
      pairConstantFactor p * pairBaseFactor p W * pairDComp p D *
        pairAComp p D A * pairTailFactor p W := by
  have hv : 0 < 1 - 1 / (p : ℝ) := by
    have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hp2le : 2 ≤ p := hp.two_le
    have hpNat1 : 1 < p := by omega
    have hpR1 : (1 : ℝ) < p := by exact_mod_cast hpNat1
    have hfrac : 1 / (p : ℝ) < 1 := (div_lt_one hpR).2 hpR1
    linarith
  have hvle : 1 - 1 / (p : ℝ) ≤ 1 := by
    have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hfrac : 0 < 1 / (p : ℝ) := by positivity
    linarith
  have hvInv : 1 ≤ (1 - 1 / (p : ℝ))⁻¹ := (one_le_inv₀ hv).2 hvle
  have hTail : 1 ≤ pairTailFactor p W := by
    by_cases h : W < (p : ℝ)
    · simp [pairTailFactor, h]
      positivity
    · simp [pairTailFactor, h]
  by_cases hp2 : p = 2
  · subst p
    have hWnot : ¬ W < (2 : ℝ) := not_lt_of_ge hW2
    by_cases hD : 2 ∣ D <;> by_cases hA2 : 2 ∈ A
      <;> simp [pairLocalFactor, pairConstantFactor, pairBaseFactor, pairDComp,
        pairAComp, pairTailFactor, hW2, hWnot, hD, hA2] <;> norm_num
  · have hp2le : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hconst : pairConstantFactor p = 1 := by simp [pairConstantFactor, hp2]
    by_cases hD : p ∣ D
    · have hbaseD : 1 ≤ pairBaseFactor p W * pairDComp p D := by
        by_cases hpW : (p : ℝ) ≤ W
        · have heq : pairBaseFactor p W * pairDComp p D =
              (1 - 1 / (p : ℝ)) ^ 3 * ((1 - 1 / (p : ℝ)) ^ 3)⁻¹ := by
            simp [pairBaseFactor, hpW, pairDComp, hD]
          have hv3ne : (1 - 1 / (p : ℝ)) ^ 3 ≠ 0 := pow_ne_zero _ hv.ne'
          rw [heq]
          rw [mul_inv_cancel₀ hv3ne]
        · have hv2 : (1 - 1 / (p : ℝ)) ^ 2 ≤ 1 := by
            calc
              (1 - 1 / (p : ℝ)) ^ 2 =
                  (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := by ring
              _ ≤ (1 - 1 / (p : ℝ)) * 1 :=
                mul_le_mul_of_nonneg_left hvle hv.le
              _ ≤ 1 := by simpa using hvle
          have hv2pos : 0 < (1 - 1 / (p : ℝ)) ^ 2 := pow_pos hv 2
          have hinv2 : 1 ≤ ((1 - 1 / (p : ℝ)) ^ 2)⁻¹ :=
            (one_le_inv₀ hv2pos).2 hv2
          have heq : pairBaseFactor p W * pairDComp p D =
              ((1 - 1 / (p : ℝ)) ^ 2)⁻¹ := by
            calc
              pairBaseFactor p W * pairDComp p D =
                  (1 - 1 / (p : ℝ)) * ((1 - 1 / (p : ℝ)) ^ 3)⁻¹ := by
                simp [pairBaseFactor, hpW, pairDComp, hD]
              _ = ((1 - 1 / (p : ℝ)) ^ 2)⁻¹ := by
                field_simp [ne_of_gt hv]
                <;> ring
          calc
            1 ≤ ((1 - 1 / (p : ℝ)) ^ 2)⁻¹ := hinv2
            _ = pairBaseFactor p W * pairDComp p D := heq.symm
      have hlocal : pairLocalFactor p W D P A = 1 := by
        simp [pairLocalFactor, hp3, hD]
      have hAcomp : pairAComp p D A = 1 := by simp [pairAComp, hD]
      calc
        pairLocalFactor p W D P A = 1 := hlocal
        _ ≤ pairBaseFactor p W * pairDComp p D := hbaseD
        _ ≤ pairBaseFactor p W * pairDComp p D * pairTailFactor p W :=
          le_mul_of_one_le_right (by positivity) hTail
        _ = pairConstantFactor p * pairBaseFactor p W * pairDComp p D *
              pairAComp p D A * pairTailFactor p W := by simp [hconst, hAcomp]
    · by_cases hpW : (p : ℝ) ≤ W
      · by_cases hpA : p ∈ A
        · have hpP : p ∈ P := hA hpA
          have hL : pairLocalFactor p W D P A =
              (1 - 1 / (p : ℝ)) ^ 2 := by
            simp [pairLocalFactor, hp3, hD, hpW, hpA, hpP,
              pairDensity_true_false p hp]
            have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
            field_simp [hpR]
            <;> ring
          have hR : pairConstantFactor p * pairBaseFactor p W * pairDComp p D *
                pairAComp p D A * pairTailFactor p W =
              (1 - 1 / (p : ℝ)) ^ 2 := by
            simp [hconst, pairBaseFactor, hpW, pairDComp, hD,
              pairAComp, hpA, pairTailFactor, not_lt_of_ge hpW]
            field_simp [ne_of_gt hv]
          rw [hL, hR]
        · have hL : pairLocalFactor p W D P A =
              1 - pairDensity p true true := by
            simp [pairLocalFactor, hp3, hD, hpW, hpA]
          have hle := (banned_factor_bound p hp hp3).1
          simpa [hconst, pairBaseFactor, hpW, pairDComp, hD,
            pairAComp, hpA, pairTailFactor, not_lt_of_ge hpW, hL] using hle
      · have hWlt : W < (p : ℝ) := lt_of_not_ge hpW
        have hpnotQW : p ∉ QW := by
          intro hpQ
          exact (not_le_of_gt hWlt) (hQWle p hpQ)
        have hpnotP : p ∉ P := fun hmem => hpnotQW (hP hmem)
        have hpnotA : p ∉ A := fun hmem => hpnotP (hA hmem)
        have hL : pairLocalFactor p W D P A =
            1 - pairDensity p false true := by
          simp [pairLocalFactor, hp3, hD, hpW, hpnotP, hpnotA]
        have hle := (banned_factor_bound p hp hp3).2
        simpa [hconst, pairBaseFactor, hpW, pairDComp, hD,
          pairAComp, hpnotA, hD, pairTailFactor, hWlt, hL] using hle

def telescopingTerm (n : ℕ) : ℝ := 2 / ((n : ℝ) - 1) - 2 / (n : ℝ)

theorem telescoping_sum (k : ℕ) :
    (∑ n ∈ Finset.Ico 3 (k + 3), telescopingTerm n) =
      1 - 2 / ((k : ℝ) + 2) := by
  induction k with
  | zero => norm_num [telescopingTerm]
  | succ k ih =>
      have htop : 3 ≤ k + 3 := by omega
      rw [show k + 3 + 1 = (k + 3) + 1 by omega,
        Finset.sum_Ico_succ_top htop]
      rw [ih]
      simp only [telescopingTerm, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [show (k : ℝ) + 3 - 1 = (k : ℝ) + 2 by ring,
        show (k : ℝ) + 1 + 2 = (k : ℝ) + 3 by ring]
      ring

theorem reciprocal_square_sum_bound (N : ℕ) :
    (∑ n ∈ Finset.Icc 3 N, (2 : ℝ) / (n : ℝ) ^ 2) ≤ 2 := by
  by_cases hN : 3 ≤ N
  · have hIcc : Finset.Icc 3 N = Finset.Ico 3 (N + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc]
    have hle :
        (∑ n ∈ Finset.Ico 3 (N + 1), (2 : ℝ) / (n : ℝ) ^ 2) ≤
          ∑ n ∈ Finset.Ico 3 (N + 1), (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn3 : 3 ≤ n := (Finset.mem_Ico.mp hn).1
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn1Nat : 1 < n := by omega
      have hn1Real : (1 : ℝ) < n := by exact_mod_cast hn1Nat
      have hn1 : 0 < (n : ℝ) - 1 := by linarith
      have hn3Real : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)
        (by positivity : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1))]
      nlinarith [hn3Real]
    have hsumEq :
        (∑ n ∈ Finset.Ico 3 (N + 1), (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) =
          ∑ n ∈ Finset.Ico 3 (N + 1), telescopingTerm n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn3 : 3 ≤ n := (Finset.mem_Ico.mp hn).1
      have hn1Nat : 1 < n := by omega
      have hn1Real : (1 : ℝ) < n := by exact_mod_cast hn1Nat
      have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
      have hn0Nat : 0 < n := by omega
      have hn0Real : (0 : ℝ) < n := by exact_mod_cast hn0Nat
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn0Real
      simp only [telescopingTerm]
      field_simp [hn1, hn0]
      ring
    have htel :
        (∑ n ∈ Finset.Ico 3 (N + 1), telescopingTerm n) = 1 - 2 / (N : ℝ) := by
      have hk : N - 2 + 3 = N + 1 := by omega
      rw [← hk, telescoping_sum]
      congr 1
      have hNcastNat : N - 2 + 2 = N := by omega
      have hNcast : ((N - 2 : ℕ) : ℝ) + 2 = N := by exact_mod_cast hNcastNat
      rw [hNcast]
    have hNpos : 0 ≤ (N : ℝ) := by positivity
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hratio : 0 ≤ 2 / (N : ℝ) := by positivity
    have hright : 1 - 2 / (N : ℝ) ≤ 2 := by linarith
    exact le_trans (le_trans hle (by rw [hsumEq])) (by rw [htel]; exact hright)
  · have hEmpty : Finset.Icc 3 N = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      exact hN (le_trans hn'.1 hn'.2)
    simp [hEmpty]

theorem tail_product_bound (Q : Finset ℕ) (W : ℝ) (N : ℕ) (hW2 : 2 ≤ W)
    (hQ : Q.filter (fun p => 3 ≤ p) ⊆ Finset.Icc 3 N) :
    (∏ p ∈ Q, if W < (p : ℝ) then 1 + 2 / (p : ℝ) ^ 2 else 1) ≤ Real.exp 2 := by
  classical
  let R : Finset ℕ := Q.filter fun p : ℕ => W < (p : ℝ)
  have hR : R ⊆ Finset.Icc 3 N := by
    intro p hp
    have hpQ : p ∈ Q := (Finset.mem_filter.mp hp).1
    have hpW : W < (p : ℝ) := (Finset.mem_filter.mp hp).2
    have hp3 : 3 ≤ p := by
      have h2p : (2 : ℝ) < p := lt_of_le_of_lt hW2 hpW
      have h2pNat : 2 < p := by exact_mod_cast h2p
      omega
    exact hQ (Finset.mem_filter.mpr ⟨hpQ, hp3⟩)
  have hsumR : (∑ p ∈ R, (2 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
    calc
      (∑ p ∈ R, (2 : ℝ) / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Finset.Icc 3 N, (2 : ℝ) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hR (by
          intro p hp hnot
          positivity)
      _ ≤ 2 := reciprocal_square_sum_bound N
  have hprodEq :
      (∏ p ∈ Q, if W < (p : ℝ) then 1 + 2 / (p : ℝ) ^ 2 else 1) =
        ∏ p ∈ R, (1 + 2 / (p : ℝ) ^ 2) := by
    simp [R, Finset.prod_filter]
  rw [hprodEq]
  have hprod := Real.prod_one_add_le_exp_sum R
    (f := fun p => (2 : ℝ) / (p : ℝ) ^ 2) (by intro p; positivity)
  exact le_trans hprod (Real.exp_le_exp.mpr hsumR)

def pairFiniteProduct (Q : Finset ℕ) (W : ℝ) (D : ℕ) (P A : Finset ℕ) : ℝ :=
  ∏ p ∈ Q, pairLocalFactor p W D P A

theorem pair_finite_product_bound (Q QW P A : Finset ℕ) (W : ℝ) (D N : ℕ)
    (hW2 : 2 ≤ W) (hQ2 : 2 ∈ Q) (hQprime : ∀ p ∈ Q, p.Prime)
    (hQWle : ∀ p ∈ QW, (p : ℝ) ≤ W) (hP : P ⊆ QW) (hA : A ⊆ P)
    (hQsmall : Q.filter (fun p => 3 ≤ p) ⊆ Finset.Icc 3 N) :
    pairFiniteProduct Q W D P A ≤
      8 * Real.exp 2 * (∏ p ∈ Q, pairBaseFactor p W) *
        (∏ p ∈ Q, pairDComp p D) * (∏ p ∈ Q, pairAComp p D A) := by
  classical
  have hlocalNonneg : ∀ p ∈ Q, 0 ≤ pairLocalFactor p W D P A := by
    intro p hpQ
    have hp := hQprime p hpQ
    by_cases hpBad : 3 ≤ p ∧ ¬ p ∣ D
    · have hdensity := pair_density_bound p hp hpBad.1
        (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))
      have hFactor : 0 ≤ 1 - pairDensity p (decide ((p : ℝ) ≤ W))
          (decide (p ∉ P ∨ p ∉ A)) := by
        have hupper : pairDensity p (decide ((p : ℝ) ≤ W))
            (decide (p ∉ P ∨ p ∉ A)) ≤ 7 / 9 := hdensity.2.2
        linarith
      simpa [pairLocalFactor, hpBad] using hFactor
    · simp [pairLocalFactor, hpBad]
  have hpoint : ∀ p ∈ Q,
      pairLocalFactor p W D P A ≤ pairConstantFactor p * pairBaseFactor p W *
        pairDComp p D * pairAComp p D A * pairTailFactor p W := by
    intro p hpQ
    exact pair_local_factor_bound p W D QW P A (hQprime p hpQ) hW2 hQWle hP hA
  have hprod : (∏ p ∈ Q, pairLocalFactor p W D P A) ≤
      ∏ p ∈ Q, pairConstantFactor p * pairBaseFactor p W * pairDComp p D *
        pairAComp p D A * pairTailFactor p W := by
    exact Finset.prod_le_prod₀ hlocalNonneg hpoint
  have hconstProd : (∏ p ∈ Q, pairConstantFactor p) = 8 := by
    rw [← Finset.insert_erase hQ2, Finset.prod_insert (by simp)]
    simp [pairConstantFactor]
  have htailProd : (∏ p ∈ Q, pairTailFactor p W) ≤ Real.exp 2 :=
    tail_product_bound Q W N hW2 hQsmall
  have hfactorized :
      (∏ p ∈ Q,
        pairConstantFactor p * pairBaseFactor p W * pairDComp p D *
          pairAComp p D A * pairTailFactor p W) =
        (∏ p ∈ Q, pairConstantFactor p) * (∏ p ∈ Q, pairBaseFactor p W) *
          (∏ p ∈ Q, pairDComp p D) * (∏ p ∈ Q, pairAComp p D A) *
            (∏ p ∈ Q, pairTailFactor p W) := by
    simp [Finset.prod_mul_distrib, mul_assoc]
  have hbaseNonneg : 0 ≤ ∏ p ∈ Q, pairBaseFactor p W := by
    apply Finset.prod_nonneg
    intro p hpQ
    have hp := hQprime p hpQ
    have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hv : 0 < 1 - 1 / (p : ℝ) := by
      have hp2 : 2 ≤ p := hp.two_le
      have hpNat1 : 1 < p := by omega
      have hpR1 : (1 : ℝ) < p := by exact_mod_cast hpNat1
      have hfrac : 1 / (p : ℝ) < 1 := (div_lt_one hpR).2 hpR1
      linarith
    by_cases hpW : (p : ℝ) ≤ W
    · simpa [pairBaseFactor, hpW] using (pow_nonneg hv.le 3)
    · simpa [pairBaseFactor, hpW] using hv.le
  have hDNonneg : 0 ≤ ∏ p ∈ Q, pairDComp p D := by
    apply Finset.prod_nonneg
    intro p hpQ
    have hp := hQprime p hpQ
    have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hp2 : 2 ≤ p := hp.two_le
    have hpNat1 : 1 < p := by omega
    have hpR1 : (1 : ℝ) < p := by exact_mod_cast hpNat1
    have hfrac : 1 / (p : ℝ) < 1 := (div_lt_one hpR).2 hpR1
    have hv : 0 < 1 - 1 / (p : ℝ) := by linarith
    unfold pairDComp
    split_ifs <;> positivity
  have hANonneg : 0 ≤ ∏ p ∈ Q, pairAComp p D A := by
    apply Finset.prod_nonneg
    intro p hpQ
    have hp := hQprime p hpQ
    have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hp2 : 2 ≤ p := hp.two_le
    have hpNat1 : 1 < p := by omega
    have hpR1 : (1 : ℝ) < p := by exact_mod_cast hpNat1
    have hfrac : 1 / (p : ℝ) < 1 := (div_lt_one hpR).2 hpR1
    have hv : 0 < 1 - 1 / (p : ℝ) := by linarith
    unfold pairAComp
    split_ifs <;> positivity
  calc
    pairFiniteProduct Q W D P A ≤
        ∏ p ∈ Q,
          pairConstantFactor p * pairBaseFactor p W * pairDComp p D *
            pairAComp p D A * pairTailFactor p W := by
      simpa [pairFiniteProduct] using hprod
    _ = (∏ p ∈ Q, pairConstantFactor p) * (∏ p ∈ Q, pairBaseFactor p W) *
          (∏ p ∈ Q, pairDComp p D) * (∏ p ∈ Q, pairAComp p D A) *
            (∏ p ∈ Q, pairTailFactor p W) := hfactorized
    _ ≤ 8 * Real.exp 2 * (∏ p ∈ Q, pairBaseFactor p W) *
          (∏ p ∈ Q, pairDComp p D) * (∏ p ∈ Q, pairAComp p D A) := by
      rw [hconstProd]
      have hcoeff : 0 ≤ (8 : ℝ) * (∏ p ∈ Q, pairBaseFactor p W) *
          (∏ p ∈ Q, pairDComp p D) * (∏ p ∈ Q, pairAComp p D A) := by
        positivity
      calc
        8 * (∏ p ∈ Q, pairBaseFactor p W) * (∏ p ∈ Q, pairDComp p D) *
            (∏ p ∈ Q, pairAComp p D A) * (∏ p ∈ Q, pairTailFactor p W) ≤
          8 * (∏ p ∈ Q, pairBaseFactor p W) * (∏ p ∈ Q, pairDComp p D) *
            (∏ p ∈ Q, pairAComp p D A) * Real.exp 2 :=
          mul_le_mul_of_nonneg_left htailProd hcoeff
        _ = 8 * Real.exp 2 * (∏ p ∈ Q, pairBaseFactor p W) *
              (∏ p ∈ Q, pairDComp p D) * (∏ p ∈ Q, pairAComp p D A) := by ring



end

end Erdos821.P9Core
