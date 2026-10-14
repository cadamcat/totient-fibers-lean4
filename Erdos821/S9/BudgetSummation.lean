import Erdos821.S9.AssignmentSiftedTask
import Erdos821.S9.SieveAggregation
import Erdos821.S9.BoxGeometry

noncomputable section
open scoped BigOperators
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core

theorem assignmentSiftedSum_le_budget
    (C : CandidateData) (x M N A K : ℝ) (jstar : ℕ)
    (hx : 1 ≤ x) (hM : 1 ≤ M) (hN : 1 ≤ N) (hMN : M * N ≤ 5 * x)
    (hK : 0 ≤ K) (hHP : 0 ≤ C.bands.harmonicP x)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g)
    (hsize : ∀ (m : MicroAssignments C x jstar)
      (marks : GlobalMarkChoices (C.bands.groups x)),
      (assignmentModulus C x jstar m marks : ℝ) ≤ x ^ (1 / 20 : ℝ))
    (hbudget : ∀ (m : MicroAssignments C x jstar)
      (marks : GlobalMarkChoices (C.bands.groups x)),
      assignmentPrimeLower C x jstar m marks →
      assignmentSiftedAverage C x M N jstar m marks ≤
        K * (((((⌈2 * M⌉₊ - ⌈M⌉₊ : ℕ) : ℝ) *
              ((⌈2 * N⌉₊ - ⌈N⌉₊ : ℕ) : ℝ)) /
              (assignmentModulus C x jstar m marks : ℝ)) *
              sieveProduct (W x) ^ 2 * sieveProduct (x ^ C.theta) * C.bands.harmonicP x +
          ((assignmentModulus C x jstar m marks : ℝ) * x ^ (0.1 : ℝ) +
            x ^ (0.59 : ℝ)) * L x ^ A)) :
    assignmentSiftedSum C x M N jstar ≤
      20 * K *
        (x * sieveProduct (W x) ^ 2 * sieveProduct (x ^ C.theta) * C.bands.harmonicP x +
          x ^ (0.64 : ℝ) * L x ^ A) * microHarmonicMass C x jstar := by
  classical
  let H : ℝ := x ^ (1 / 20 : ℝ)
  let area : ℝ := ((⌈2 * M⌉₊ - ⌈M⌉₊ : ℕ) : ℝ) *
    ((⌈2 * N⌉₊ - ⌈N⌉₊ : ℕ) : ℝ)
  let V : ℝ := sieveProduct (W x) ^ 2 * sieveProduct (x ^ C.theta) * C.bands.harmonicP x
  let a : ℝ := K * area * V
  let b : ℝ := K * x ^ (0.1 : ℝ) * L x ^ A
  let c : ℝ := K * x ^ (0.59 : ℝ) * L x ^ A
  let counts := fun (m : MicroAssignments C x jstar)
    (marks : GlobalMarkChoices (C.bands.groups x)) =>
      if assignmentPrimeLower C x jstar m marks then
        assignmentSiftedAverage C x M N jstar m marks else 0
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hL : 0 ≤ L x := Real.log_nonneg hx
  have hV : 0 ≤ V := mul_nonneg
    (mul_nonneg (sq_nonneg _) (sieveProduct_pos _).le) hHP
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg hK (by dsimp [area]; positivity)) hV
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcounts m marks : counts m marks ≤
      a / (assignmentModulus C x jstar m marks : ℝ) +
        b * (assignmentModulus C x jstar m marks : ℝ) + c := by
    dsimp [counts]
    by_cases hp : assignmentPrimeLower C x jstar m marks
    · rw [if_pos hp]
      have h := hbudget m marks hp
      convert h using 1 <;> dsimp [a, b, c, V, area] <;> ring
    · rw [if_neg hp]
      exact add_nonneg (add_nonneg (div_nonneg ha (Nat.cast_nonneg _))
        (mul_nonneg hb (Nat.cast_nonneg _))) hc
  have hsum := assignment_sieve_sum_bound C x H a b c jstar
    (by dsimp [H]; positivity) hb hc hmass hsize counts hcounts
  have hsum' : assignmentSiftedSum C x M N jstar ≤
      (a + b * H ^ 2 + c * H) * microHarmonicMass C x jstar := by
    simpa only [assignmentSiftedSum, counts, mul_ite, mul_zero] using hsum
  have hH2 : H ^ 2 = x ^ (0.1 : ℝ) := by
    dsimp [H]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have hpow1 : x ^ (0.1 : ℝ) * H ^ 2 ≤ x ^ (0.64 : ℝ) := by
    rw [hH2, ← Real.rpow_add hxpos]
    apply Real.rpow_le_rpow_of_exponent_le hx
    norm_num
  have hpow2 : x ^ (0.59 : ℝ) * H = x ^ (0.64 : ℝ) := by
    dsimp [H]
    rw [← Real.rpow_add hxpos]
    norm_num
  have harea : area ≤ 20 * x := dyadic_area_le x M N hx hM hN hMN
  have hmain : a ≤ 20 * K * (x * V) := by
    dsimp [a]
    nlinarith [mul_le_mul_of_nonneg_right harea (mul_nonneg hK hV)]
  have herr1 : b * H ^ 2 ≤ K * (x ^ (0.64 : ℝ) * L x ^ A) := by
    dsimp [b]
    nlinarith [mul_le_mul_of_nonneg_right hpow1
      (mul_nonneg hK (Real.rpow_nonneg hL A))]
  have herr2 : c * H = K * (x ^ (0.64 : ℝ) * L x ^ A) := by
    dsimp [c]
    calc
      _ = K * (x ^ (0.59 : ℝ) * H) * L x ^ A := by ring
      _ = _ := by rw [hpow2]; ring
  have hscalar : a + b * H ^ 2 + c * H ≤
      20 * K * (x * V + x ^ (0.64 : ℝ) * L x ^ A) := by
    rw [herr2]
    have hE : 0 ≤ K * (x ^ (0.64 : ℝ) * L x ^ A) := by positivity
    nlinarith [hmain, herr1]
  have hmicro : 0 ≤ microHarmonicMass C x jstar := by
    unfold microHarmonicMass listNormalizer
    positivity
  simpa only [V, mul_assoc] using
    hsum'.trans (mul_le_mul_of_nonneg_right hscalar hmicro)

end Erdos821.S56Core

