import Erdos821.P9.PairSieveData
import Erdos821.Blueprint.Classical

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos821.Blueprint

private theorem pairBadCount_le_three_mul (p : ℕ) (belowW banned : Bool) :
    pairBadCount p belowW banned ≤ 3 * p := by
  cases belowW <;> cases banned <;> simp [pairBadCount] <;> omega

theorem pairBadCount_product_le_d_three_pow_omega (d : ℕ) (W : ℝ)
    (P A : Finset ℕ) (hsq : Squarefree d)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p) :
    (∏ p : d.primeFactors,
      pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A))) ≤
      d * 3 ^ d.primeFactors.card := by
  classical
  let Q := d.primeFactors
  have hprod :
      (∏ p ∈ Q, pairBadCount p (decide ((p : ℝ) ≤ W))
        (decide (p ∉ P ∨ p ∉ A))) ≤ ∏ p ∈ Q, 3 * p := by
    apply Finset.prod_le_prod
    intro p hp
    exact pairBadCount_le_three_mul p _ _
  have hcoe :
      (∏ p : d.primeFactors,
        pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A))) =
      ∏ p ∈ Q, pairBadCount p (decide ((p : ℝ) ≤ W))
        (decide (p ∉ P ∨ p ∉ A)) := by
    exact Finset.prod_coe_sort Q
      (fun p : ℕ => pairBadCount p (decide ((p : ℝ) ≤ W))
        (decide (p ∉ P ∨ p ∉ A)))
  rw [hcoe]
  calc
    (∏ p ∈ Q, pairBadCount p (decide ((p : ℝ) ≤ W))
        (decide (p ∉ P ∨ p ∉ A))) ≤ ∏ p ∈ Q, 3 * p := hprod
    _ = (∏ p ∈ Q, (3 : ℕ)) * (∏ p ∈ Q, p) := by rw [Finset.prod_mul_distrib]
    _ = d * 3 ^ d.primeFactors.card := by
      simp [Q, Nat.prod_primeFactors_of_squarefree hsq, Nat.mul_comm]

theorem three_pow_primeFactors_le_divisor_card_sq (n : ℕ) (hn : n ≠ 0) :
    3 ^ n.primeFactors.card ≤ n.divisors.card ^ 2 := by
  classical
  let Q := n.primeFactors
  have hfactor : ∀ p ∈ Q, 2 ≤ n.factorization p + 1 := by
    intro p hp
    have hpd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpos : 0 < n.factorization p := hprime.factorization_pos_of_dvd hn hpd
    omega
  have hprod :
      2 ^ Q.card ≤ ∏ p ∈ Q, (n.factorization p + 1) := by
    calc
      2 ^ Q.card = ∏ p ∈ Q, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ Q, (n.factorization p + 1) := by
        apply Finset.prod_le_prod
        intro p hp
        exact hfactor p hp
  have hcard : n.divisors.card = ∏ p ∈ Q, (n.factorization p + 1) := by
    exact Nat.card_divisors hn
  have htwo : 2 ^ Q.card ≤ n.divisors.card := by
    rw [hcard]
    exact hprod
  have hsq : (2 ^ Q.card) * (2 ^ Q.card) ≤ n.divisors.card * n.divisors.card :=
    Nat.mul_le_mul htwo htwo
  have hfour : (4 : ℕ) ^ Q.card = (2 ^ Q.card) * (2 ^ Q.card) := by
    calc
      (4 : ℕ) ^ Q.card = (2 * 2) ^ Q.card := by norm_num
      _ = 2 ^ Q.card * 2 ^ Q.card := by rw [mul_pow]
  calc
    3 ^ Q.card ≤ 4 ^ Q.card :=
      pow_le_pow_left' (show (3 : ℕ) ≤ 4 by omega) Q.card
    _ = (2 ^ Q.card) * (2 ^ Q.card) := hfour
    _ ≤ n.divisors.card * n.divisors.card := hsq
    _ = n.divisors.card ^ 2 := by ring

/-- A sharper remainder estimate retains the local factor `3^ω(d)`. -/
theorem pairSieveData_remainder_bound_strong
    (a b c e D d : ℕ) (W : ℝ) (P A Q : Finset ℕ)
    (hab : a ≤ b) (hce : c ≤ e) (hD : 0 < D) (hd : 0 < d)
    (hcop : Nat.Coprime D d) (hsq : Squarefree d)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p)
    (hQprime : ∀ p ∈ Q, p.Prime) :
    |(pairSieveData a b c e D W P A Q hD hQprime).remainder d| ≤
      4 * (D : ℝ) * d * 3 ^ d.primeFactors.card +
        2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * 3 ^ d.primeFactors.card := by
  classical
  let S := pairSieveData a b c e D W P A Q hD hQprime
  let r := D * d
  let width : ℝ := ((b - a : ℕ) : ℝ) * (e - c : ℕ)
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  letI : NeZero r := ⟨Nat.ne_of_gt (Nat.mul_pos hD hd)⟩
  letI : ∀ p : d.primeFactors, NeZero p.val := fun p =>
    ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  let R : Finset (ZMod r × ZMod r) := Finset.univ.filter fun v =>
    pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧
      ∀ p : d.primeFactors,
        pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A))
          (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)
  have hX : S.X = (Nat.totient D : ℝ) * width / (D : ℝ) ^ 2 := by
    simp [S, pairSieveData, width]
    <;> ring
  have hlocalDensity (p : d.primeFactors) :
      S.density p.val =
        (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ) / (p.val : ℝ) ^ 2 := by
    change pairDensity p.val (decide ((p.val : ℝ) ≤ W))
      (decide (p.val ∉ P ∨ p.val ∉ A)) = _
    rw [pairDensity, ← pairBadCount_cast_eq_pairNu p.val (hd3 p.val p.property)]
  have hG : S.g d =
      (∏ p ∈ d.primeFactors,
        (pairBadCount p (decide ((p : ℝ) ≤ W))
          (decide (p ∉ P ∨ p ∉ A)) : ℝ)) / (d : ℝ) ^ 2 := by
    change (∏ p ∈ d.primeFactors, S.density p) = _
    calc
      _ = ∏ p ∈ d.primeFactors,
          (pairBadCount p (decide ((p : ℝ) ≤ W))
            (decide (p ∉ P ∨ p ∉ A)) : ℝ) / (p : ℝ) ^ 2 := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hlocalDensity ⟨p, hp⟩
      _ = (∏ p ∈ d.primeFactors,
            (pairBadCount p (decide ((p : ℝ) ≤ W))
              (decide (p ∉ P ∨ p ∉ A)) : ℝ)) / (d : ℝ) ^ 2 := by
        rw [Finset.prod_div_distrib]
        have hpProd : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
          rw [← Nat.cast_prod]
          exact_mod_cast Nat.prod_primeFactors_of_squarefree hsq
        rw [Finset.prod_pow, hpProd]
  have hcountSubtype :
      (∏ p : d.primeFactors,
        (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) =
      ∏ p ∈ d.primeFactors,
        (pairBadCount p (decide ((p : ℝ) ≤ W))
          (decide (p ∉ P ∨ p ∉ A)) : ℝ) := by
    exact Finset.prod_coe_sort (d.primeFactors : Finset ℕ)
      (fun p : ℕ => (pairBadCount p (decide ((p : ℝ) ≤ W))
        (decide (p ∉ P ∨ p ∉ A)) : ℝ))
  have hcenter : S.X * S.g d =
      (Nat.totient D : ℝ) *
        (∏ p : d.primeFactors,
          (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) *
        width / (r : ℝ) ^ 2 := by
    rw [hX, hG, ← hcountSubtype]
    dsimp [width, r]
    rw [Nat.cast_mul]
    have hDc : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
    have hdc : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp [hDc, hdc]
    <;> ring
  have hfilter0 := pairSieveData_local_filter_eq_crtRoots
    a b c e D d W P A Q hD hQprime
  have hfilterS :
      (S.objects.filter fun z => ∀ p ∈ d.primeFactors, S.bad p z) =
        (Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
          (fun z => pairResidue r z ∈ R) := by
    simpa [S, r, R] using hfilter0
  have hrem : S.remainder d =
      ((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
        (fun z => pairResidue r z ∈ R)).card - S.X * S.g d := by
    have hw : ∀ z ∈ S.objects, S.weight z = 1 := by intro z hz; rfl
    rw [sieveRemainder_eq_filtered_card S d hw, hfilterS]
  have hrootCard : R.card = Nat.totient D *
      ∏ p : d.primeFactors,
        pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) := by
    simpa [R, Fintype.card_subtype] using
      pair_crt_divisibility_root_count D d W P A hcop
        (Nat.ne_of_gt hD) (Nat.ne_of_gt hd) hsq hd3
  have hrootLe : R.card ≤ D * d * 3 ^ d.primeFactors.card := by
    rw [hrootCard]
    calc
      Nat.totient D *
          (∏ p : d.primeFactors,
            pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
              (decide (p.val ∉ P ∨ p.val ∉ A))) ≤
          D * (d * 3 ^ d.primeFactors.card) :=
        Nat.mul_le_mul (Nat.totient_le D)
          (pairBadCount_product_le_d_three_pow_omega d W P A hsq hd3)
      _ = D * d * 3 ^ d.primeFactors.card := by ring
  have hrootCardReal : (R.card : ℝ) =
      (Nat.totient D : ℝ) *
        (∏ p : d.primeFactors,
          (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
            (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) := by
    exact_mod_cast hrootCard
  have hgrid := pair_grid_count_area_error a b c e r hab hce
    (Nat.mul_pos hD hd) R
  have hgridMain :
      (R.card : ℝ) * ((b - a : ℕ) : ℝ) * (e - c : ℕ) / (r : ℝ) ^ 2 =
        S.X * S.g d := by
    calc
      _ = (Nat.totient D : ℝ) *
          (∏ p : d.primeFactors,
            (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
              (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) *
          width / (r : ℝ) ^ 2 := by rw [hrootCardReal]; ring
      _ = S.X * S.g d := hcenter.symm
  have hgrid' :
      |(((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
          fun z => pairResidue r z ∈ R).card : ℝ) - S.X * S.g d| ≤
        (D : ℝ) * d * 3 ^ d.primeFactors.card *
          (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := by
    rw [← hgridMain]
    calc
      _ ≤ (R.card : ℝ) *
          (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := hgrid
      _ ≤ ((D : ℝ) * d * 3 ^ d.primeFactors.card) *
          (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hrootLe
  rw [hrem]
  calc
    |(((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
        fun z => pairResidue r z ∈ R).card : ℝ) - S.X * S.g d| ≤
      (D : ℝ) * d * 3 ^ d.primeFactors.card *
        (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := hgrid'
    _ = 4 * (D : ℝ) * d * 3 ^ d.primeFactors.card +
        2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) *
          3 ^ d.primeFactors.card := by
      dsimp [r]
      rw [Nat.cast_mul]
      have hDc : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      have hdc : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
      field_simp [hDc, hdc]
      <;> ring

theorem pairSieveData_remainderSum_bound_divisors
    (hc : ClassicalInputs) (a b c e D : ℕ) (level : ℝ)
    (W : ℝ) (P A Q : Finset ℕ)
    (hab : a ≤ b) (hce : c ≤ e) (hD : 0 < D)
    (hlevel : 1 ≤ level)
    (hQprime : ∀ p ∈ Q, p.Prime)
    (hQlarge : ∀ p ∈ Q, 3 ≤ p) (hQnotD : ∀ p ∈ Q, ¬p∣D) :
    ∃ Cτ Kτ : ℝ, 0 < Kτ ∧
      let S := pairSieveData a b c e D W P A Q hD hQprime
      S.remainderSum level ≤
        (4 * (D : ℝ) * (⌊level⌋₊ : ℝ) ^ 2 +
          2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * (⌊level⌋₊ : ℝ)) *
          Kτ * (Real.log (2 * (⌊level⌋₊ : ℝ))) ^ Cτ := by
  classical
  let S := pairSieveData a b c e D W P A Q hD hQprime
  let N := ⌊level⌋₊
  obtain ⟨Cτ, Kτ, hKτ, hMoment⟩ := hc.divisors 2
  have hN : 1 ≤ N := by
    dsimp [N]
    exact (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ level)).2
      (by exact_mod_cast hlevel)
  have hmomentN := (hMoment (N : ℝ) (by exact_mod_cast hN)).2
  have hmomentBound :
      (∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) ^ 2) ≤
        Kτ * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ Cτ := by
    simpa [Nat.floor_natCast] using hmomentN
  have hsubset : S.products level ⊆ Finset.Icc 1 N := by
    exact Finset.filter_subset _ _
  have hpoint : ∀ d ∈ S.products level,
      |S.remainder d| ≤
        4 * (D : ℝ) * d * 3 ^ d.primeFactors.card +
          2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * 3 ^ d.primeFactors.card := by
    intro d hdS
    have hmem := Finset.mem_filter.mp hdS
    have hd1 := (Finset.mem_Icc.mp hmem.1).1
    have hdpos : 0 < d := by omega
    rcases hmem.2 with ⟨hsq, hdPrimes⟩
    have hcop : Nat.Coprime D d := by
      by_contra hnotcop
      obtain ⟨p, hp, hpD, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnotcop
      have hpFactor : p ∈ d.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.ne_of_gt hdpos⟩
      exact hQnotD p (hdPrimes hpFactor) hpD
    have hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p := by
      intro p hp
      exact hQlarge p (hdPrimes hp)
    exact pairSieveData_remainder_bound_strong a b c e D d W P A Q
      hab hce hD hdpos hcop hsq hd3 hQprime
  have hpowBound : ∀ d ∈ Finset.Icc 1 N,
      (3 : ℝ) ^ d.primeFactors.card ≤ (d.divisors.card : ℝ) ^ 2 := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hnat := three_pow_primeFactors_le_divisor_card_sq d (Nat.ne_of_gt hdpos)
    exact_mod_cast hnat
  have hsumPow :
      (∑ d ∈ S.products level, (3 : ℝ) ^ d.primeFactors.card) ≤
        Kτ * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ Cτ := by
    calc
      (∑ d ∈ S.products level, (3 : ℝ) ^ d.primeFactors.card) ≤
          ∑ d ∈ S.products level, (d.divisors.card : ℝ) ^ 2 :=
        Finset.sum_le_sum (by
          intro d hd
          exact hpowBound d (hsubset hd))
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro d hd hnot
          positivity)
      _ ≤ Kτ * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ Cτ := hmomentBound
  have hsumD :
      (∑ d ∈ S.products level,
        (d : ℝ) * (3 : ℝ) ^ d.primeFactors.card) ≤
        (N : ℝ) * (Kτ * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ Cτ) := by
    calc
      _ ≤ ∑ d ∈ S.products level,
          (N : ℝ) * (3 : ℝ) ^ d.primeFactors.card := by
        apply Finset.sum_le_sum
        intro d hd
        have hdle : d ≤ N := (Finset.mem_Icc.mp (hsubset hd)).2
        have hcast : (d : ℝ) ≤ N := by exact_mod_cast hdle
        exact mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = (N : ℝ) * ∑ d ∈ S.products level,
          (3 : ℝ) ^ d.primeFactors.card := by rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumPow (by positivity)
  have hsumErrors :
      (∑ d ∈ S.products level, |S.remainder d|) ≤
        4 * (D : ℝ) *
            ((N : ℝ) * (Kτ * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ Cτ)) +
          2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) *
            (Kτ * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ Cτ) := by
    calc
      _ ≤ ∑ d ∈ S.products level,
          (4 * (D : ℝ) * d * 3 ^ d.primeFactors.card +
            2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) *
              3 ^ d.primeFactors.card) := Finset.sum_le_sum hpoint
      _ = 4 * (D : ℝ) *
            (∑ d ∈ S.products level, (d : ℝ) * 3 ^ d.primeFactors.card) +
          2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) *
            (∑ d ∈ S.products level, 3 ^ d.primeFactors.card) := by
        calc
          _ = ∑ d ∈ S.products level,
                (4 * (D : ℝ) * ((d : ℝ) * 3 ^ d.primeFactors.card) +
                  2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) *
                    3 ^ d.primeFactors.card) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hsumD (by positivity)
        · exact mul_le_mul_of_nonneg_left hsumPow (by positivity)
  refine ⟨Cτ, Kτ, hKτ, ?_⟩
  change (∑ d ∈ S.products level, |S.remainder d|) ≤ _
  calc
    (∑ d ∈ S.products level, |S.remainder d|) ≤
        4 * (D : ℝ) * ((N : ℝ) *
            (Kτ * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ Cτ)) +
          2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) *
            (Kτ * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ Cτ) := hsumErrors
    _ = (4 * (D : ℝ) * (N : ℝ) ^ 2 +
          2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * (N : ℝ)) *
          Kτ * (Real.log (2 * (N : ℝ))) ^ Cτ := by ring


end

end Erdos821.P9Core
