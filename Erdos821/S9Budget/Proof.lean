import Erdos821.S9.PairBudgetTask
import Erdos821.P9.StrongRemainder
import Erdos821.S9.SieveAggregation

set_option maxHeartbeats 0

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.S9Budget

open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core
attribute [local instance] Classical.propDecidable

theorem sqrt_le_mul_of_ge (a y : ℝ) (ha : 0 < a)
    (hy : (1 / a) ^ 2 ≤ y) (hy0 : 0 < y) :
    Real.sqrt y ≤ a * y := by
  have hrecip : 0 < 1 / a := by positivity
  have hroot : 1 / a ≤ Real.sqrt y := by
    rw [← Real.sqrt_sq hrecip.le]
    exact Real.sqrt_le_sqrt hy
  have hmul : 1 ≤ a * Real.sqrt y := by
    have h := mul_le_mul_of_nonneg_left hroot ha.le
    have hcan : a * (1 / a) = 1 := by field_simp [ha.ne']
    rw [hcan] at h
    linarith
  have hsq : y = Real.sqrt y * Real.sqrt y :=
    (Real.mul_self_sqrt hy0.le).symm
  calc
    Real.sqrt y = 1 * Real.sqrt y := by ring
    _ ≤ (a * Real.sqrt y) * Real.sqrt y :=
      mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg _)
    _ = a * (Real.sqrt y * Real.sqrt y) := by ring
    _ = a * y := congrArg (fun t : ℝ => a * t) hsq.symm

theorem pairSieveData_densityBounds_explicit
    (a b c e D : ℕ) (W z : ℝ) (P A Q : Finset ℕ)
    (hD : 0 < D) (hW2 : 2 ≤ W) (hWz : W ≤ z) (hz : 1 < z)
    (hQsubset : Q ⊆ primesUpTo z)
    (hQprime : ∀ p ∈ Q, p.Prime) (hQlarge : ∀ p ∈ Q, 3 ≤ p)
    (hQnotD : ∀ p ∈ Q, ¬ p ∣ D)
    (hPsubset : P ⊆ primesUpTo W) (hAsubset : A ⊆ P)
    (Kₘ : ℝ)
    (hM : ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ primesUpTo y, (p : ℝ)⁻¹) - Real.log (Real.log y)| ≤ Kₘ) :
    (pairSieveData a b c e D W P A Q hD hQprime).densityBounds z (2 / 9)
      (3 * (Real.log 2 + 2 * Kₘ) + 1) := by
  classical
  have hKₘ0 : 0 ≤ Kₘ := by
    have htwo := hM 2 (by norm_num)
    exact le_trans (abs_nonneg _) htwo
  let C₀ : ℝ := 3 * (Real.log 2 + 2 * Kₘ) + 1
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  let S := pairSieveData a b c e D W P A Q hD hQprime
  have hInterval (w : ℝ) (hw : 1 < w) :
      (∑ p ∈ Q.filter fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ (2 : ℕ),
        S.density p) ≤ C₀ := by
    let I := Q.filter fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ (2 : ℕ)
    have hlocal (p : ℕ) (hp : p ∈ I) : S.density p ≤ 3 / (p : ℝ) := by
      have hpQ := (Finset.mem_filter.mp hp).1
      have hpP := hQprime p hpQ
      have hp3 := hQlarge p hpQ
      simpa [S, pairSieveData] using (pair_density_bound p hpP hp3
        (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))).2.1
    have hIle : (∑ p ∈ I, S.density p) ≤ 3 * (∑ p ∈ I, (p : ℝ)⁻¹) := by
      calc
        _ ≤ ∑ p ∈ I, 3 / (p : ℝ) := Finset.sum_le_sum (by
          intro p hp
          exact hlocal p hp)
        _ = 3 * (∑ p ∈ I, (p : ℝ)⁻¹) := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.mul_sum]
    by_cases hw2 : 2 ≤ w
    · let Qlo := primesUpTo w
      let Qhi := primesUpTo (w ^ 2)
      have hWw2 : w ≤ w ^ 2 := by nlinarith
      have hQlo : Qlo ⊆ Qhi := by
        apply primesUpTo_mono hWw2 (by linarith) (by positivity)
      have hIsub : I ⊆ Qhi \ Qlo := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpQ, ⟨hwp, hpw2⟩⟩
        have hpPrime := hQprime p hpQ
        have hpHi : p ∈ Qhi :=
          (mem_primesUpTo_iff (w ^ 2) (by positivity) p).2 ⟨hpPrime, hpw2⟩
        have hpNotLo : p ∉ Qlo := by
          intro hpLo
          exact (not_lt_of_ge
            ((mem_primesUpTo_iff w (by linarith) p).1 hpLo).2) hwp
        exact Finset.mem_sdiff.mpr ⟨hpHi, hpNotLo⟩
      have hrecipDiff :
          (∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹) =
            (∑ p ∈ Qhi, (p : ℝ)⁻¹) - ∑ p ∈ Qlo, (p : ℝ)⁻¹ := by
        have hsum :
            (∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹) +
                ∑ p ∈ Qlo, (p : ℝ)⁻¹ =
              ∑ p ∈ Qhi, (p : ℝ)⁻¹ := Finset.sum_sdiff hQlo
        linarith
      have hhighBound :
          (∑ p ∈ Qhi, (p : ℝ)⁻¹) - Real.log (Real.log (w ^ 2)) ≤ Kₘ :=
        (abs_le.mp (hM (w ^ 2) (by nlinarith))).2
      have hlowBound : Real.log (Real.log w) -
          (∑ p ∈ Qlo, (p : ℝ)⁻¹) ≤ Kₘ := by
        have h := (abs_le.mp (hM w (by linarith))).1
        linarith
      have hlogRatio :
          Real.log (Real.log (w ^ 2)) - Real.log (Real.log w) = Real.log 2 := by
        have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
        rw [Real.log_pow]
        norm_num1
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlogw)]
        ring
      have hrecipI : (∑ p ∈ I, (p : ℝ)⁻¹) ≤ Real.log 2 + 2 * Kₘ := by
        calc
          (∑ p ∈ I, (p : ℝ)⁻¹) ≤ ∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hIsub (by
              intro p hp hnot
              exact inv_nonneg.mpr (Nat.cast_nonneg p))
          _ = (∑ p ∈ Qhi, (p : ℝ)⁻¹) - ∑ p ∈ Qlo, (p : ℝ)⁻¹ := hrecipDiff
          _ ≤ Real.log (Real.log (w ^ 2)) - Real.log (Real.log w) + 2 * Kₘ := by
            linarith [hhighBound, hlowBound]
          _ = Real.log 2 + 2 * Kₘ := by rw [hlogRatio]
      have hILeC : (∑ p ∈ I, S.density p) ≤ C₀ := by
        calc
          _ ≤ 3 * (∑ p ∈ I, (p : ℝ)⁻¹) := hIle
          _ ≤ 3 * (Real.log 2 + 2 * Kₘ) := by nlinarith
          _ ≤ C₀ := by dsimp [C₀]; linarith
      simpa [I] using hILeC
    · have hwLt : w < 2 := lt_of_not_ge hw2
      have hwSq : w ^ 2 < 4 := by nlinarith
      have hIone : I ⊆ {3} := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpQ, ⟨hwp, hpw2⟩⟩
        have hpNat := hQlarge p hpQ
        have hpLt : (p : ℝ) < 4 := lt_of_le_of_lt hpw2 hwSq
        have hpNatLt : p < 4 := by exact_mod_cast hpLt
        have hpeq : p = 3 := by omega
        simp [hpeq]
      have hIleOne : (∑ p ∈ I, S.density p) ≤ 1 := by
        calc
          _ ≤ ∑ p ∈ I, 1 := Finset.sum_le_sum (by
            intro p hp
            have hpQ := (Finset.mem_filter.mp hp).1
            have h := (pair_density_bound p (hQprime p hpQ) (hQlarge p hpQ)
              (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))).2.2
            simpa [S, pairSieveData] using
              (h.trans (by norm_num : (7 / 9 : ℝ) ≤ 1)))
          _ ≤ ∑ p ∈ ({3} : Finset ℕ), (1 : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hIone (by
              intro p hp hnot
              norm_num)
          _ = 1 := by simp
      have hILeC : (∑ p ∈ I, S.density p) ≤ C₀ := by
        calc
          _ ≤ 1 := hIleOne
          _ ≤ C₀ := by dsimp [C₀]; linarith [hKₘ0, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
      simpa [I] using hILeC
  have hW0 : 0 ≤ W := by linarith
  have hz0 : 0 ≤ z := le_trans hW0 hWz
  refine ⟨hz, by norm_num, ?_, ?_⟩
  · intro p hp
    have hpPrime := hQprime p hp
    have hpz := (mem_primesUpTo_iff z hz0 p).1 (hQsubset hp)
    have hlocal := pair_density_bound p hpPrime (hQlarge p hp)
      (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))
    constructor
    · exact hpz.2
    constructor
    · exact hlocal.1
    · have hDensity : S.density p ≤ 7 / 9 := by
        simpa [S, pairSieveData] using hlocal.2.2
      calc
        S.density p ≤ 7 / 9 := hDensity
        _ ≤ 1 - 2 / 9 := by norm_num
  · intro w hw
    simpa [S, pairSieveData] using hInterval w hw

theorem pairSieveData_remainderSum_bound_uniform (hc : ClassicalInputs) :
    ∃ Cτ Kτ : ℝ, 0 < Kτ ∧
      ∀ (a b c e D : ℕ) (level : ℝ) (W : ℝ) (P A Q : Finset ℕ)
        (hab : a ≤ b) (hce : c ≤ e) (hD : 0 < D) (hlevel : 1 ≤ level)
        (hQprime : ∀ p ∈ Q, p.Prime) (hQlarge : ∀ p ∈ Q, 3 ≤ p)
        (hQnotD : ∀ p ∈ Q, ¬ p ∣ D),
        let S := pairSieveData a b c e D W P A Q hD hQprime
        S.remainderSum level ≤
          (4 * (D : ℝ) * (⌊level⌋₊ : ℝ) ^ 2 +
            2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * (⌊level⌋₊ : ℝ)) *
            Kτ * (Real.log (2 * (⌊level⌋₊ : ℝ))) ^ Cτ := by
  classical
  obtain ⟨Cτ, Kτ, hKτ, hMoment⟩ := hc.divisors 2
  refine ⟨Cτ, Kτ, hKτ, ?_⟩
  intro a b c e D level W P A Q hab hce hD hlevel hQprime hQlarge hQnotD
  let S := pairSieveData a b c e D W P A Q hD hQprime
  let N := ⌊level⌋₊
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

def logMomentFactor (A : ℝ) : ℝ :=
  max 1 (max ((Real.log 2) ^ A) (3 ^ max A 0))

theorem logMoment_majorant (x Y A : ℝ) (hx : 4 ≤ x) (hL : 3 ≤ L x)
    (hY : 1 ≤ Y) (hYx : Y ≤ x ^ 2) :
    Real.log (2 * Y) ^ A ≤ logMomentFactor A * L x ^ max A 0 := by
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hargpos : 0 < 2 * Y := by positivity
  have hargupper : 2 * Y ≤ 2 * x ^ 2 := by nlinarith
  have hzupper : Real.log (2 * Y) ≤ 3 * L x := by
    change Real.log (2 * Y) ≤ 3 * Real.log x
    have hu := Real.log_le_log hargpos hargupper
    have hx2ne : x ^ 2 ≠ 0 := pow_ne_zero _ hxpos.ne'
    rw [Real.log_mul (by norm_num) hx2ne, Real.log_pow] at hu
    norm_num1 at hu
    have hLlog : 3 ≤ Real.log x := by simpa [L] using hL
    nlinarith [hlog2le]
  have harglower : 2 ≤ 2 * Y := by nlinarith
  have hzlower : Real.log 2 ≤ Real.log (2 * Y) :=
    Real.log_le_log (by norm_num) harglower
  have hzpos : 0 < Real.log (2 * Y) := hlog2pos.trans_le hzlower
  by_cases hA : 0 ≤ A
  · have hD : max A 0 = A := max_eq_left hA
    have hpow := Real.rpow_le_rpow (x := Real.log (2 * Y))
      (y := 3 * L x) (z := A) (le_of_lt hzpos) hzupper hA
    have hmul : (3 * L x) ^ A = 3 ^ A * L x ^ A :=
      Real.mul_rpow (by norm_num) (le_of_lt hLpos)
    have hK : 3 ^ A ≤ logMomentFactor A := by
      dsimp [logMomentFactor]
      rw [hD]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    calc
      Real.log (2 * Y) ^ A ≤ (3 * L x) ^ A := hpow
      _ = 3 ^ A * L x ^ A := hmul
      _ ≤ logMomentFactor A * L x ^ max A 0 := by
        rw [hD]
        exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (le_of_lt hLpos) A)
  · have hAneg : A < 0 := lt_of_not_ge hA
    have hD : max A 0 = 0 := max_eq_right (le_of_lt hAneg)
    have hinv : (Real.log (2 * Y))⁻¹ ≤ (Real.log 2)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hlog2pos hzlower
    have hpow := Real.rpow_le_rpow (x := (Real.log (2 * Y))⁻¹)
      (y := (Real.log 2)⁻¹) (z := -A) (by positivity) hinv (by linarith)
    have hident (z : ℝ) : z ^ A = z⁻¹ ^ (-A) := by
      calc
        z ^ A = z ^ (-(-A)) := by congr 1 <;> ring
        _ = z⁻¹ ^ (-A) := Real.rpow_neg_eq_inv_rpow z (-A)
    have hK : (Real.log 2) ^ A ≤ logMomentFactor A := by
      dsimp [logMomentFactor]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    calc
      Real.log (2 * Y) ^ A = (Real.log (2 * Y))⁻¹ ^ (-A) := hident _
      _ ≤ (Real.log 2)⁻¹ ^ (-A) := hpow
      _ = (Real.log 2) ^ A := by rw [← hident]
      _ ≤ logMomentFactor A := hK
      _ = logMomentFactor A * L x ^ max A 0 := by simp [hD]

theorem dyadic_nat_width_le (M : ℝ) (hM : 0 ≤ M) :
    ((⌈2 * M⌉₊ - ⌈M⌉₊ : ℕ) : ℝ) ≤ M + 1 := by
  have hceil : ⌈M⌉₊ ≤ ⌈2 * M⌉₊ := Nat.ceil_mono (by linarith)
  rw [Nat.cast_sub hceil]
  have hlo := Nat.le_ceil M
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2 * M by linarith)
  linarith

theorem sieveProduct_pos (y : ℝ) : 0 < sieveProduct y := by
  unfold sieveProduct
  apply Finset.prod_pos
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpCast : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
  have hpPos : 0 < (p : ℝ) := Nat.cast_pos.mpr hpPrime.pos
  have hfrac : 1 / (p : ℝ) < 1 := (div_lt_one hpPos).2 hpCast
  have hbase : 0 < 1 - 1 / (p : ℝ) := sub_pos.mpr hfrac
  simpa [one_div] using hbase

theorem pairAComp_nonneg_of_prime (p D : ℕ) (A : Finset ℕ)
    (hp : p.Prime) : 0 ≤ pairAComp p D A := by
  by_cases h : p ∈ A ∧ ¬ p ∣ D
  · rw [pairAComp, if_pos h]
    have hpCast : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hpPos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hfrac : 1 / (p : ℝ) < 1 := (div_lt_one hpPos).2 hpCast
    have hbase : 0 < 1 - 1 / (p : ℝ) := sub_pos.mpr hfrac
    exact inv_nonneg.mpr (by simpa [one_div] using hbase.le)
  · simp [pairAComp, h]

theorem permissionMaskProbability_nonneg (P : Finset ℕ)
    (allow : PermissionIndex P → Bool) :
    0 ≤ permissionMaskProbability P (1 / 2) allow := by
  unfold permissionMaskProbability
  apply Finset.prod_nonneg
  intro p hp
  cases hv : allow p <;> norm_num [hv]

theorem permissionAllowed_subset (R : Finset ℕ) (allow : PermissionIndex R → Bool) :
    S56Core.permissionAllowed R allow ⊆ R := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  exact q.property

theorem groupPrimeSet_subset_primeUpTo_W
    (C : CandidateData) (x : ℝ)
    (hb : C.bands.geometry.b = 1 / 5)
    (hd : C.bands.geometry.d = 2 / 5)
    (hAd : Admissible C.bands.geometry x (C.bands.groups x))
    (hL : 1 ≤ L x) :
    groupPrimeSet (C.bands.groups x) ⊆ primesUpTo (W x) := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨g, hg⟩
  have hbound := hAd.2.2.2.1 g p hg.2
  have hpUpper : (p : ℝ) ≤ Real.exp (L x ^ (2 / 5 : ℝ)) := by
    by_cases hsmall : g ∈ (C.bands.groups x).small
    · simp only [if_pos hsmall] at hbound
      have hu := hbound.2
      have hsmallExp : L x ^ (1 / 5 : ℝ) ≤ L x ^ (2 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      have hu' : (p : ℝ) ≤ Real.exp (L x ^ (1 / 5 : ℝ)) := by
        simpa [hb] using hu
      exact hu'.trans (Real.exp_le_exp.mpr hsmallExp)
    · simp only [if_neg hsmall] at hbound
      simpa [hd] using hbound.2
  have hpow : L x ^ (2 / 5 : ℝ) ≤ Real.sqrt (L x) := by
    calc
      L x ^ (2 / 5 : ℝ) ≤ L x ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = Real.sqrt (L x) := (Real.sqrt_eq_rpow _).symm
  have hprimebound : (p : ℝ) ≤ W x := by
    change (p : ℝ) ≤ Real.exp (Real.sqrt (L x))
    exact hpUpper.trans (Real.exp_le_exp.mpr hpow)
  have hW0 : 0 ≤ W x := by
    change 0 ≤ Real.exp (Real.sqrt (L x))
    exact (Real.exp_pos _).le
  exact (mem_primesUpTo_iff (W x) hW0 p).2
    ⟨(C.bands.groups x).prime g p hg.2, hprimebound⟩

theorem totient_box_density_bound (D : ℕ) (u v : ℝ) (hD : 0 < D)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((Nat.totient D : ℝ) * u * v) / (D : ℝ) ^ 2 ≤ (u * v) / (D : ℝ) := by
  have hDreal : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have htot : (Nat.totient D : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.totient_le D
  have hratio : (Nat.totient D : ℝ) / (D : ℝ) ≤ 1 :=
    (div_le_iff₀ hDreal).2 (by linarith)
  have harea : 0 ≤ u * v := mul_nonneg hu hv
  calc
    ((Nat.totient D : ℝ) * u * v) / (D : ℝ) ^ 2 =
        ((Nat.totient D : ℝ) / (D : ℝ)) * ((u * v) / (D : ℝ)) := by
      field_simp [ne_of_gt hDreal]
      <;> ring
    _ ≤ 1 * ((u * v) / (D : ℝ)) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg harea hDreal.le)
    _ = (u * v) / (D : ℝ) := by ring

theorem pairSieveBudgetTask_proof : S56Core.PairSieveBudgetTask := by
  intro hc hs hDivTask hMaskTask δ C hC
  have hCOriginal := hC
  rcases hC with
    ⟨hBandValid, hC1eq, hC2eq, hRatioEq, hSEq, hDelta, hScale, hPrefix,
      hGap, hQeq, hEllEq, hGeomA, hGeomB, hGeomC, hGeomD, hMicro,
      hThetaLower, hThetaUpper, hTheta10, hThetaExtra, hPsiSmooth,
      hPsiSupport, hPsiNonneg, hPsiInterval⟩
  rcases hBandValid with
    ⟨hR0, hBandC1Pos, hBandC1C2, hBandSPos, hBandRatio, hBandSmall,
      hBandGap, hBandLast, hBandTail⟩
  rcases hBandTail with ⟨cmin, cmax, hcmin, hcmax, hBandEvents⟩
  have hAdmissibleEventually :
      ∀ᶠ x : ℝ in atTop, Admissible C.bands.geometry x (C.bands.groups x) := by
    filter_upwards [hBandEvents] with x hx
    exact hx.1
  have hThetaPos : 0 < C.theta := by
    have hc2pos : 0 < C.bands.c₂ := hBandC1Pos.trans hBandC1C2
    have hleft : 0 < C.bands.c₂ * C.bands.s' / (2 : ℝ) ^ C.micro := by
      positivity
    linarith
  have htheta10' : 10 * C.theta ≤ (1 / 20 : ℝ) := by
    exact hTheta10
  rcases hc.mertens.1 with ⟨Kₘ, hMertens⟩
  have hKₘ0 : 0 ≤ Kₘ := by
    have htwo := hMertens 2 (by norm_num)
    exact le_trans (abs_nonneg _) htwo
  let C₀ : ℝ := 3 * (Real.log 2 + 2 * Kₘ) + 1
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  rcases hs.block (2 / 9) C₀ (by norm_num) hC₀ with
    ⟨Kblock, hKblock, hblock0, hblock⟩
  obtain ⟨Cτ, Kτ, hKτ, hRemainder⟩ :=
    pairSieveData_remainderSum_bound_uniform hc
  rcases hDivTask with ⟨Kdiv, hKdiv, hDivEventually⟩
  have hMaskEventually := hMaskTask δ C hCOriginal
  have hLtop : Tendsto (fun x : ℝ => L x) atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop
  have hLargeEventually : ∀ᶠ x : ℝ in atTop,
      4 ≤ x ∧ 3 ≤ L x ∧ (1 / C.theta) ^ 2 ≤ L x := by
    filter_upwards [eventually_ge_atTop (4 : ℝ),
      hLtop.eventually_ge_atTop 3,
      hLtop.eventually_ge_atTop ((1 / C.theta) ^ 2)] with x hx4 hxL hxTheta
    exact ⟨hx4, hxL, hxTheta⟩
  let Aerr : ℝ := max Cτ 0
  let logFactor : ℝ := logMomentFactor Cτ
  have hlogFactorPos : 0 < logFactor := by
    dsimp [logFactor, logMomentFactor]
    positivity
  let Kmain : ℝ := Kblock * (8 * Real.exp 2) * Kdiv
  let Kerror : ℝ := Kblock * (8 * Kτ * logFactor)
  let Ktotal : ℝ := Kmain + Kerror
  have hKmain : 0 < Kmain := by dsimp [Kmain]; positivity
  have hKerror : 0 < Kerror := by dsimp [Kerror]; positivity
  have hKtotal : 0 < Ktotal := by dsimp [Ktotal]; positivity
  refine ⟨Aerr, Ktotal, hKtotal, ?_⟩
  filter_upwards [hLargeEventually, hDivEventually, hMaskEventually,
      hAdmissibleEventually] with x hx hDivX hMaskX hAd
  rcases hx with ⟨hx4, hL3, hLTheta⟩
  intro M N D R hD hM0 hN0 hMx hNx hDsize hDprime hR
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hxgtone : 1 < x := by linarith
  have hLpos : 0 < L x := by linarith
  have hLone : 1 ≤ L x := by linarith
  have hsqrtScale : Real.sqrt (L x) ≤ C.theta * L x :=
    sqrt_le_mul_of_ge C.theta (L x) hThetaPos hLTheta hLpos
  let z : ℝ := x ^ C.theta
  have hz : 1 < z := by
    dsimp [z]
    have hpow := Real.rpow_lt_rpow_of_exponent_lt hxgtone hThetaPos
    simpa using hpow
  have hz0 : 0 ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 1) hz.le
  have hW2 : 2 ≤ W x := by
    have hroot : 1 ≤ Real.sqrt (L x) := by
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt (L x) := Real.sqrt_le_sqrt (by linarith)
    have hexp : 2 ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      linarith
    change 2 ≤ Real.exp (Real.sqrt (L x))
    exact hexp.trans (Real.exp_le_exp.mpr hroot)
  have hWz : W x ≤ z := by
    change Real.exp (Real.sqrt (L x)) ≤ x ^ C.theta
    rw [Real.rpow_def_of_pos hxpos]
    exact Real.exp_le_exp.mpr (by simpa [L, mul_comm] using hsqrtScale)
  have hlevel : 1 ≤ z ^ (10 : ℕ) := by
    dsimp [z]
    exact one_le_pow₀ hz.le
  have hlevelPow : z ^ (10 : ℕ) ≤ x ^ (1 / 20 : ℝ) := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by nlinarith [hTheta10])
  have hLxBound : 3 ≤ L x := hL3
  let level : ℝ := z ^ (10 : ℕ)
  let nlevel : ℕ := ⌊level⌋₊
  have hnlevelGe : 1 ≤ nlevel := by
    dsimp [nlevel, level]
    exact (Nat.le_floor_iff (by positivity)).2 (by exact_mod_cast hlevel)
  have hnlevelCast : (nlevel : ℝ) ≤ x ^ (1 / 20 : ℝ) := by
    dsimp [nlevel, level]
    exact (Nat.floor_le (by positivity)).trans hlevelPow
  have hnlevelSquare : (nlevel : ℝ) ^ 2 ≤ x ^ (1 / 10 : ℝ) := by
    have hpowSquare : (x ^ (1 / 20 : ℝ)) ^ 2 = x ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      congr 1 <;> norm_num
    calc
      (nlevel : ℝ) ^ 2 = (nlevel : ℝ) * nlevel := by ring
      _ ≤ (x ^ (1 / 20 : ℝ)) * x ^ (1 / 20 : ℝ) :=
        mul_le_mul hnlevelCast hnlevelCast (by positivity) (by positivity)
      _ = x ^ (1 / 10 : ℝ) := by rw [← hpowSquare]; ring
  have hxPowOne : x ^ (1 / 20 : ℝ) ≤ x := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hxone
      (by norm_num : (1 / 20 : ℝ) ≤ 1)
    simpa using hpow
  have hnlevelX2Nat : (nlevel : ℝ) ≤ x ^ (2 : ℕ) := by
    calc
      (nlevel : ℝ) ≤ x ^ (1 / 20 : ℝ) := hnlevelCast
      _ ≤ x := hxPowOne
      _ ≤ x ^ (2 : ℕ) := by nlinarith [hxone]
  have hlogRem := logMoment_majorant x (nlevel : ℝ) Cτ hx4 hLxBound
    (by exact_mod_cast hnlevelGe) hnlevelX2Nat
  have hx054 : 1 ≤ x ^ (0.54 : ℝ) := by
    calc
      1 = x ^ (0 : ℝ) := by simp
      _ ≤ x ^ (0.54 : ℝ) := Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
  let wm : ℝ := ((⌈2 * M⌉₊ - ⌈M⌉₊ : ℕ) : ℝ)
  let wn : ℝ := ((⌈2 * N⌉₊ - ⌈N⌉₊ : ℕ) : ℝ)
  have hceilM : ⌈M⌉₊ ≤ ⌈2 * M⌉₊ := Nat.ceil_mono (by linarith)
  have hceilN : ⌈N⌉₊ ≤ ⌈2 * N⌉₊ := Nat.ceil_mono (by linarith)
  have hwm0 : 0 ≤ wm := by
    dsimp [wm]
    exact Nat.cast_nonneg _
  have hwn0 : 0 ≤ wn := by
    dsimp [wn]
    exact Nat.cast_nonneg _
  have hwmBound : wm ≤ M + 1 := by
    simpa [wm] using dyadic_nat_width_le M hM0
  have hwnBound : wn ≤ N + 1 := by
    simpa [wn] using dyadic_nat_width_le N hN0
  have hwidthSum : wm + wn ≤ 4 * x ^ (0.54 : ℝ) := by
    linarith [hwmBound, hwnBound, hMx, hNx, hx054]
  let area : ℝ := wm * wn
  have harea0 : 0 ≤ area := by dsimp [area]; positivity
  let Xlo : ℝ := area / (D : ℝ)
  have hwidthSquare : 4 * (D : ℝ) * (nlevel : ℝ) ^ 2 ≤
      4 * (D : ℝ) * x ^ (1 / 10 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hnlevelSquare (by positivity)
  have hwidthRemainder :
      2 * (wm + wn) * (nlevel : ℝ) ≤ 8 * x ^ (0.59 : ℝ) := by
    have hprodBound : x ^ (0.54 : ℝ) * x ^ (1 / 20 : ℝ) ≤
        x ^ (0.59 : ℝ) := by
      have heq : x ^ (0.54 : ℝ) * x ^ (1 / 20 : ℝ) = x ^ (0.59 : ℝ) := by
        rw [← Real.rpow_add hxpos]
        congr 1 <;> norm_num
      exact le_of_eq heq
    have hmul := mul_le_mul hwidthSum hnlevelCast (by positivity)
      (by positivity : 0 ≤ 4 * x ^ (0.54 : ℝ))
    calc
      2 * (wm + wn) * (nlevel : ℝ) ≤
          8 * (x ^ (0.54 : ℝ) * x ^ (1 / 20 : ℝ)) := by nlinarith
      _ ≤ 8 * x ^ (0.59 : ℝ) := mul_le_mul_of_nonneg_left hprodBound (by norm_num)
  have herrorCore :
      (4 * (D : ℝ) * (nlevel : ℝ) ^ 2 +
        2 * (wm + wn) * (nlevel : ℝ)) ≤
      8 * ((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) := by
    have hDreal : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
    have hxPowEq : x ^ (1 / 10 : ℝ) = x ^ (0.1 : ℝ) := by congr 1 <;> norm_num
    rw [hxPowEq] at hwidthSquare
    calc
      _ ≤ 4 * (D : ℝ) * x ^ (0.1 : ℝ) + 8 * x ^ (0.59 : ℝ) :=
        add_le_add hwidthSquare hwidthRemainder
      _ ≤ 8 * ((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) := by nlinarith
  have herrorBound :
      (4 * (D : ℝ) * (nlevel : ℝ) ^ 2 +
        2 * (wm + wn) * (nlevel : ℝ)) * Kτ *
          (Real.log (2 * (nlevel : ℝ))) ^ Cτ ≤
        8 * Kτ * logFactor *
          (((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) *
            L x ^ Aerr) := by
    have hlogBase : 0 < Real.log (2 * (nlevel : ℝ)) := by
      apply Real.log_pos
      have hnNat : 1 < 2 * nlevel := by omega
      exact_mod_cast hnNat
    have hlogPow0 : 0 ≤ (Real.log (2 * (nlevel : ℝ))) ^ Cτ :=
      Real.rpow_nonneg hlogBase.le Cτ
    have hlogCompare :
        (Real.log (2 * (nlevel : ℝ))) ^ Cτ ≤ logFactor * L x ^ Aerr := by
      dsimp [logFactor, Aerr]
      exact hlogRem
    calc
      _ ≤ (8 * ((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) * Kτ) *
            (Real.log (2 * (nlevel : ℝ))) ^ Cτ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right herrorCore (le_of_lt hKτ)) hlogPow0
      _ = (8 * ((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) * Kτ) *
            (Real.log (2 * (nlevel : ℝ))) ^ Cτ := by ring
      _ ≤ (8 * ((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) * Kτ) *
            (logFactor * L x ^ Aerr) :=
        mul_le_mul_of_nonneg_left hlogCompare (by positivity)
      _ = 8 * Kτ * logFactor *
            (((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) *
              L x ^ Aerr) := by ring
  have hLpow0 : 0 ≤ L x ^ Aerr := Real.rpow_nonneg hLpos.le _
  let errorTerm : ℝ :=
    ((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) * L x ^ Aerr
  have herrorTerm0 : 0 ≤ errorTerm := by
    dsimp [errorTerm]
    positivity
  have hRemUniform (allow : PermissionIndex R → Bool) :
      (S56Core.pairBudgetData C x M N D R hD allow).remainderSum level ≤
        8 * Kτ * logFactor * errorTerm := by
    have hceilMle : ⌈M⌉₊ ≤ ⌈2 * M⌉₊ := hceilM
    have hceilNle : ⌈N⌉₊ ≤ ⌈2 * N⌉₊ := hceilN
    have hQprimeLocal : ∀ p ∈ S56Core.pairBudgetPrimes C x D, p.Prime := by
      intro p hp
      exact (mem_primesUpTo_iff z hz0 p).1
        (Finset.mem_filter.mp hp).1 |>.1
    have hQlargeLocal : ∀ p ∈ S56Core.pairBudgetPrimes C x D, 3 ≤ p := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2.1
    have hQnotDLocal : ∀ p ∈ S56Core.pairBudgetPrimes C x D, ¬ p ∣ D := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2.2
    have hrem' := hRemainder (⌈M⌉₊) (⌈2 * M⌉₊) (⌈N⌉₊) (⌈2 * N⌉₊)
      D level (W x) (groupPrimeSet (C.bands.groups x))
      (S56Core.permissionAllowed R allow) (S56Core.pairBudgetPrimes C x D)
      hceilMle hceilNle hD hlevel hQprimeLocal hQlargeLocal hQnotDLocal
    have hremCast :
      (S56Core.pairBudgetData C x M N D R hD allow).remainderSum level ≤
        (4 * (D : ℝ) * (nlevel : ℝ) ^ 2 +
          2 * (wm + wn) * (nlevel : ℝ)) * Kτ *
            (Real.log (2 * (nlevel : ℝ))) ^ Cτ := by
      simpa [level, nlevel, wm, wn, S56Core.pairBudgetData,
        S56Core.pairBudgetPrimes] using hrem'
    calc
      _ ≤ (4 * (D : ℝ) * (nlevel : ℝ) ^ 2 +
          2 * (wm + wn) * (nlevel : ℝ)) * Kτ *
            (Real.log (2 * (nlevel : ℝ))) ^ Cτ := hremCast
      _ ≤ 8 * Kτ * logFactor * errorTerm := by
        simpa [errorTerm] using herrorBound
  let P : Finset ℕ := groupPrimeSet (C.bands.groups x)
  let Q : Finset ℕ := S56Core.pairBudgetPrimes C x D
  have hPsubset : P ⊆ primesUpTo (W x) := by
    exact groupPrimeSet_subset_primeUpTo_W C x hGeomB hGeomD hAd hLone
  have hRsubset : R ⊆ P := by simpa [P] using hR
  have hQsubset : Q ⊆ primesUpTo z := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hQprime : ∀ p ∈ Q, p.Prime := by
    intro p hp
    exact (mem_primesUpTo_iff z hz0 p).1
      (Finset.mem_filter.mp hp).1 |>.1
  have hQlarge : ∀ p ∈ Q, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  have hQnotD : ∀ p ∈ Q, ¬ p ∣ D := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.2
  have hQcomplete : ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ p ∣ D → p ∈ Q := by
    intro p hp hp3 hpz hpD
    have hmem : p ∈ S56Core.pairBudgetPrimes C x D := by
      unfold S56Core.pairBudgetPrimes
      exact Finset.mem_filter.mpr
        ⟨(mem_primesUpTo_iff z hz0 p).2 ⟨hp, hpz⟩, hp3, hpD⟩
    simpa [Q] using hmem
  let F : ℝ := 8 * Real.exp 2 * sieveProduct (W x) ^ 2 * sieveProduct z
  let B : ℝ := F * Kdiv
  have hSievePosW : 0 < sieveProduct (W x) := sieveProduct_pos _
  have hSievePosZ : 0 < sieveProduct z := sieveProduct_pos _
  have hXlo0 : 0 ≤ Xlo := by
    dsimp [Xlo]
    exact div_nonneg harea0 (by positivity)
  have hFpos : 0 < F := by
    dsimp [F]
    positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hTotientBound :
      ((Nat.totient D : ℝ) * wm * wn) / (D : ℝ) ^ 2 ≤ Xlo := by
    simpa [Xlo, area] using totient_box_density_bound D wm wn hD hwm0 hwn0
  have hDivComp :
      (∏ p ∈ primesUpTo z, pairDComp p D) ≤ Kdiv :=
    hDivX D z hD hDsize hDprime
  have hprobNonneg : ∀ allow : PermissionIndex R → Bool,
      0 ≤ permissionMaskProbability R C.bands.geometry.q allow := by
    intro allow
    rw [hQeq]
    exact permissionMaskProbability_nonneg R allow
  have hprobSum :
      (∑ allow : PermissionIndex R → Bool,
        permissionMaskProbability R C.bands.geometry.q allow) = 1 :=
    permissionMaskProbability_sum_eq_one R C.bands.geometry.q
  let prob := fun allow : PermissionIndex R → Bool =>
    permissionMaskProbability R C.bands.geometry.q allow
  let comp := fun allow : PermissionIndex R → Bool =>
    ∏ p ∈ primesUpTo z,
      pairAComp p D (S56Core.permissionAllowed R allow)
  have hcompNonneg : ∀ allow : PermissionIndex R → Bool, 0 ≤ comp allow := by
    intro allow
    dsimp [comp]
    apply Finset.prod_nonneg
    intro p hp
    exact pairAComp_nonneg_of_prime p D (S56Core.permissionAllowed R allow)
      ((mem_primesUpTo_iff z hz0 p).1 hp |>.1)
  have hcompAverageNonneg :
      0 ≤ ∑ allow : PermissionIndex R → Bool, prob allow * comp allow := by
    apply Finset.sum_nonneg
    intro allow ha
    exact mul_nonneg (hprobNonneg allow) (hcompNonneg allow)
  have hcompBound :
      (∑ allow : PermissionIndex R → Bool, prob allow * comp allow) ≤
        C.bands.harmonicP x := by
    simpa [prob, comp] using hMaskX R D z hRsubset
  have hHPnonneg : 0 ≤ C.bands.harmonicP x :=
    hcompAverageNonneg.trans hcompBound
  have hBnonneg : 0 ≤ B := le_of_lt hBpos
  let err : ℝ := 8 * Kτ * logFactor * errorTerm
  have herr0 : 0 ≤ err := by
    dsimp [err]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKτ.le)
      hlogFactorPos.le) herrorTerm0
  have hcount : ∀ allow : PermissionIndex R → Bool,
      (S56Core.pairBudgetData C x M N D R hD allow).sifted ≤
        Kblock * Xlo * B * comp allow + Kblock * err := by
    intro allow
    let Aset := S56Core.permissionAllowed R allow
    let S := S56Core.pairBudgetData C x M N D R hD allow
    have hAset : Aset ⊆ P := by
      change S56Core.permissionAllowed R allow ⊆ P
      exact (permissionAllowed_subset R allow).trans hR
    have hdensity := pairSieveData_densityBounds_explicit
      ⌈M⌉₊ ⌈2 * M⌉₊ ⌈N⌉₊ ⌈2 * N⌉₊ D (W x) z P Aset Q
      hD hW2 hWz hz hQsubset hQprime hQlarge hQnotD hPsubset hAset
      Kₘ hMertens
    have hdensityS : S.densityBounds z (2 / 9) C₀ := by
      simpa [S, Aset, P, Q, S56Core.pairBudgetData,
        S56Core.pairBudgetPrimes] using hdensity
    have hblockS := (hblock (ℕ × ℕ) S z hdensityS).1
    have hproductEq := pairSieveData_product_eq_pairFiniteProduct
      ⌈M⌉₊ ⌈2 * M⌉₊ ⌈N⌉₊ ⌈2 * N⌉₊ D (W x) z P Aset Q
      hD hz0 hQsubset hQcomplete hQprime hQlarge hQnotD
    have hproductBound := pair_sieve_product_bound (W x) z D P Aset
      hW2 hWz hPsubset hAset
    have hprodS : S.product ≤ B * comp allow := by
      have hDcomp := hDivComp
      have hAcomp0 : 0 ≤ comp allow := hcompNonneg allow
      calc
        S.product = pairFiniteProduct (primesUpTo z) (W x) D P Aset := by
          simpa [S, Aset, P, Q, S56Core.pairBudgetData,
            S56Core.pairBudgetPrimes] using hproductEq
        _ ≤ F * (∏ p ∈ primesUpTo z, pairDComp p D) * comp allow := by
          simpa [F, comp, Aset, S56Core.permissionAllowed] using hproductBound
        _ ≤ F * Kdiv * comp allow :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDcomp (le_of_lt hFpos)) hAcomp0
        _ = B * comp allow := by simp [B]
    have hprodNonneg : 0 ≤ S.product := by
      unfold Erdos821.Blueprint.SieveData.product
      apply Finset.prod_nonneg
      intro p hp
      have hlocal := hdensityS.2.2.1 p hp
      linarith
    have hSX : S.X = ((Nat.totient D : ℝ) * wm * wn) / (D : ℝ) ^ 2 := by
      simp [S, Aset, P, Q, wm, wn, S56Core.pairBudgetData,
        S56Core.pairBudgetPrimes, Erdos821.P9Core.pairSieveData]
    have hremS : S.remainderSum level ≤ err := by
      simpa [S, Aset, P, Q, err, errorTerm, wm, wn,
        S56Core.pairBudgetData, S56Core.pairBudgetPrimes] using hRemUniform allow
    calc
      _ ≤ Kblock * S.X * S.product + Kblock * S.remainderSum level := hblockS
      _ = Kblock * (((Nat.totient D : ℝ) * wm * wn) / (D : ℝ) ^ 2) *
            S.product + Kblock * S.remainderSum level := by rw [hSX]
      _ ≤ Kblock * Xlo * S.product + Kblock * err := by
        apply add_le_add
        · have hXle := hTotientBound
          calc
            Kblock * (((Nat.totient D : ℝ) * wm * wn) / (D : ℝ) ^ 2) * S.product =
                (Kblock * (((Nat.totient D : ℝ) * wm * wn) / (D : ℝ) ^ 2)) * S.product := by ring
            _ ≤ (Kblock * Xlo) * S.product :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hXle (le_of_lt hKblock)) hprodNonneg
            _ = Kblock * Xlo * S.product := by ring
        · exact mul_le_mul_of_nonneg_left hremS (le_of_lt hKblock)
      _ ≤ Kblock * Xlo * (B * comp allow) + Kblock * err := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hprodS
            (mul_nonneg (le_of_lt hKblock) hXlo0)
        · exact le_rfl
      _ = Kblock * Xlo * B * comp allow + Kblock * err := by ring
  have havg := S56Core.mask_sieve_average_bound
    prob (fun allow : PermissionIndex R → Bool =>
      (S56Core.pairBudgetData C x M N D R hD allow).sifted)
    comp Kblock Xlo B err (C.bands.harmonicP x)
    hprobNonneg hprobSum (le_of_lt hKblock) hXlo0 hBnonneg hcompBound hcount
  let mainTerm : ℝ := Xlo * sieveProduct (W x) ^ 2 * sieveProduct z *
    C.bands.harmonicP x
  have hmainTerm0 : 0 ≤ mainTerm := by
    dsimp [mainTerm, Xlo]
    positivity
  have herrTerm0 : 0 ≤ errorTerm := herrorTerm0
  have hMainIdentity : Kblock * Xlo * B * C.bands.harmonicP x = Kmain * mainTerm := by
    simp [Kmain, mainTerm, B, F]
    ring
  have hErrIdentity : Kblock * err = Kerror * errorTerm := by
    simp [Kerror, err, logFactor]
    ring
  calc
    (∑ allow : PermissionIndex R → Bool,
      permissionMaskProbability R C.bands.geometry.q allow *
        (S56Core.pairBudgetData C x M N D R hD allow).sifted) ≤
      Kblock * Xlo * B * C.bands.harmonicP x + Kblock * err := by
        simpa [prob] using havg
    _ = Kmain * mainTerm + Kerror * errorTerm := by rw [hMainIdentity, hErrIdentity]
    _ ≤ Ktotal * (mainTerm + errorTerm) := by
      have hcross : 0 ≤ Kmain * errorTerm + Kerror * mainTerm :=
        add_nonneg (mul_nonneg (le_of_lt hKmain) herrTerm0)
          (mul_nonneg (le_of_lt hKerror) hmainTerm0)
      dsimp [Ktotal]
      nlinarith

example : S56Core.PairSieveBudgetTask :=
  @Erdos821.S9Budget.pairSieveBudgetTask_proof


end Erdos821.S9Budget
