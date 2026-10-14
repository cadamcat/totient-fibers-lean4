import Erdos821.P7.BandGeometryTask
import Erdos821.P7.LastBand
import Erdos821.P7.BandDisjoint
import PrimeNumberTheoremAnd.Erdos970.MertensClassical

/-! Dyadic prime groups for the candidate geometry: elementary interval facts
and the reciprocal-mass estimate. -/

noncomputable section
open Filter

namespace Erdos821.P7Band
open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

/-- The first power of two strictly above `y` (when `1 ≤ y`). -/
def dyadicAbove (y : ℝ) : ℕ :=
  if h : 1 ≤ y then (exists_nat_pow_near h (show (1 : ℝ) < 2 by norm_num)).choose + 1
  else 0

theorem dyadicAbove_spec {y : ℝ} (h : 1 ≤ y) :
    y < (2 : ℝ) ^ dyadicAbove y ∧ (2 : ℝ) ^ dyadicAbove y ≤ 2 * y := by
  have hs := (exists_nat_pow_near h (show (1 : ℝ) < 2 by norm_num)).choose_spec
  simp only [dyadicAbove, h, ↓reduceDIte]
  refine ⟨hs.2, ?_⟩
  rw [pow_succ]
  linarith [hs.1]

/-- The prime group at dyadic exponent `b`: primes in `(exp (3b/2), exp (9b/5)]`. -/
def grp (b : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp (3 / 2 * b)⌋₊ ⌊Real.exp (9 / 5 * b)⌋₊).filter Nat.Prime

theorem mem_grp {b : ℝ} {p : ℕ} :
    p ∈ grp b ↔ p.Prime ∧ Real.exp (3 / 2 * b) < p ∧ (p : ℝ) ≤ Real.exp (9 / 5 * b) := by
  simp only [grp, Finset.mem_filter, Finset.mem_Ioc,
    Nat.floor_lt (Real.exp_pos _).le, Nat.le_floor_iff (Real.exp_pos _).le]
  tauto

theorem pow_two_div_le {u : ℝ} (hu : 0 ≤ u) {i j : ℕ} (hij : i ≤ j) :
    u / (2 : ℝ) ^ j ≤ u / 2 ^ i :=
  div_le_div_of_nonneg_left hu (by positivity) (pow_le_pow_right₀ (by norm_num) hij)

theorem pow_two_div_le_half {u : ℝ} (hu : 0 ≤ u) {i j : ℕ} (hij : i < j) :
    u / (2 : ℝ) ^ j ≤ u / 2 ^ i / 2 := by
  have h := pow_two_div_le hu (Nat.succ_le_of_lt hij)
  simpa only [pow_succ, div_div] using h

theorem grp_disjoint {u : ℝ} (hu : 0 < u) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (grp (u / 2 ^ i)) (grp (u / 2 ^ j)) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (grp (u / 2 ^ i)) (grp (u / 2 ^ j)) := by
    intro i j hij
    refine Finset.disjoint_left.mpr fun p hpi hpj => ?_
    obtain ⟨-, hi1, -⟩ := mem_grp.mp hpi
    obtain ⟨-, -, hj2⟩ := mem_grp.mp hpj
    have hle := pow_two_div_le_half hu.le hij
    have hpos : 0 < u / 2 ^ i := by positivity
    have : Real.exp (9 / 5 * (u / 2 ^ j)) < Real.exp (3 / 2 * (u / 2 ^ i)) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- A Q-band at exponent `u / 2^i` misses the prime group at exponent `u / 2^j`. -/
theorem band_grp_disjoint {u : ℝ} (hu : 0 < u) (i j : ℕ) {p : ℕ}
    (h1 : Real.exp (u / 2 ^ i) ≤ p) (h2 : (p : ℝ) ≤ Real.exp (6 / 5 * (u / 2 ^ i)))
    (hp : p ∈ grp (u / 2 ^ j)) : False := by
  obtain ⟨-, hg1, hg2⟩ := mem_grp.mp hp
  have ha : u / 2 ^ i ≤ 9 / 5 * (u / 2 ^ j) := Real.exp_le_exp.mp (h1.trans hg2)
  have hb : 3 / 2 * (u / 2 ^ j) < 6 / 5 * (u / 2 ^ i) := Real.exp_lt_exp.mp (hg1.trans_le h2)
  have hj : 0 < u / 2 ^ j := by positivity
  rcases lt_or_ge i j with h | h
  · have := pow_two_div_le_half hu.le h
    nlinarith
  · have := pow_two_div_le hu.le h
    nlinarith

/-! ## Reciprocal mass of a group -/

open Erdos970.Mertens in
theorem grp_mass_eventually :
    ∃ Y : ℝ, ∀ b : ℝ, 0 < b → Y ≤ Real.exp (3 / 2 * b) →
      Real.log (6 / 5) / 2 ≤ ∑ p ∈ grp b, 1 / (p : ℝ) ∧
        ∑ p ∈ grp b, 1 / (p : ℝ) ≤ 2 * Real.log (6 / 5) := by
  have hE : Tendsto E₂p atTop (nhds 0) := (Asymptotics.isLittleO_one_iff ℝ).mp E₂p.bound'
  have hl : 0 < Real.log (6 / 5) := Real.log_pos (by norm_num)
  have hev : ∀ᶠ y in atTop, |E₂p y| < Real.log (6 / 5) / 4 := by
    have := (Metric.tendsto_nhds.mp hE) (Real.log (6 / 5) / 4) (by positivity)
    simpa [Real.dist_eq] using this
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hev
  refine ⟨Y, fun b hb hYb => ?_⟩
  set lo := Real.exp (3 / 2 * b)
  set hi := Real.exp (9 / 5 * b)
  have hlohi : lo ≤ hi := Real.exp_le_exp.mpr (by linarith)
  have hfl : ⌊lo⌋₊ ≤ ⌊hi⌋₊ := Nat.floor_le_floor hlohi
  have hsplit : ∑ p ∈ grp b, 1 / (p : ℝ) =
      (∑ p ∈ Finset.Ioc 0 ⌊hi⌋₊ with p.Prime, (1 : ℝ) / p) -
        ∑ p ∈ Finset.Ioc 0 ⌊lo⌋₊ with p.Prime, (1 : ℝ) / p := by
    rw [grp, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
    ring
  rw [hsplit, sum_prime_div_eq, sum_prime_div_eq]
  have hlogs : Real.log (Real.log hi) - Real.log (Real.log lo) = Real.log (6 / 5) := by
    simp only [hi, lo, Real.log_exp]
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    norm_num
  have e1 := hY lo hYb
  have e2 := hY hi (hYb.trans hlohi)
  rw [abs_lt] at e1 e2
  constructor <;> nlinarith

end Erdos821.P7Band
