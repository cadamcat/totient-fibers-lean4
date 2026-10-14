import Erdos821.P7Band.Dyadic

/-! The prime-band family of `candidate_geometry`: dyadic P-groups in the gaps
between the Q-bands, gated to the empty family outside the eventual range. -/

noncomputable section
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Band
open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

/-! ## Real-variable facts -/

theorem T_tendsto : Tendsto T atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

theorem L_eq_exp {x : ℝ} (hL : 0 < L x) : L x = Real.exp (T x) := by
  rw [T, Real.exp_log hL]

theorem L_rpow {x r : ℝ} (hL : 0 < L x) : L x ^ r = Real.exp (T x * r) := by
  rw [Real.rpow_def_of_pos hL, T]

/-- Pure dyadic bookkeeping for one group of a family. -/
theorem range_of {u A B y : ℝ} {m k n : ℕ} (hu : 0 < u) (hA : 0 < A) (hB : 0 < B)
    (hy : y = 9 / 5 * u / B) (hy1 : y < 2 ^ m) (hy2 : (2 : ℝ) ^ m ≤ 2 * y)
    (hN : (2 : ℝ) ^ n * A * (12 / 5) ≤ B) (hk : k < n) :
    A ≤ 3 / 2 * (u / 2 ^ (m + k)) ∧ 9 / 5 * (u / 2 ^ (m + k)) ≤ B := by
  have hyB : y * B = 9 / 5 * u := by rw [hy]; field_simp
  have hy0 : 0 < y := by rw [hy]; positivity
  have hpk : (2 : ℝ) ^ (m + k) ≤ 2 ^ m * 2 ^ n := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hpm : (2 : ℝ) ^ m ≤ 2 ^ (m + k) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2mk : (0 : ℝ) < 2 ^ (m + k) := by positivity
  constructor
  · rw [mul_div_assoc', le_div_iff₀ h2mk]
    have h1 : A * 2 ^ (m + k) ≤ A * (2 * y * 2 ^ n) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      calc (2 : ℝ) ^ (m + k) ≤ 2 ^ m * 2 ^ n := hpk
        _ ≤ 2 * y * 2 ^ n := by gcongr
    have h2 : A * (2 * y * 2 ^ n) = 5 / 6 * y * (2 ^ n * A * (12 / 5)) := by ring
    have h3 : 5 / 6 * y * (2 ^ n * A * (12 / 5)) ≤ 5 / 6 * y * B := by
      apply mul_le_mul_of_nonneg_left hN; positivity
    nlinarith
  · rw [mul_div_assoc', div_le_iff₀ h2mk]
    have : B * y < B * 2 ^ (m + k) :=
      mul_lt_mul_of_pos_left (hy1.trans_le hpm) hB
    nlinarith

/-! ## Indices and the gate -/

/-- Number of groups in each family. -/
def nG (x : ℝ) : ℕ := ⌊T x / 20⌋₊

/-- Dyadic exponent `s L / 2^j`; equal to `BandData.scale` for ratio `2`. -/
def ex (s x : ℝ) (j : ℕ) : ℝ := s * L x / 2 ^ j

/-- First index of the family whose upper exponent limit is `L^β`. -/
def startIdx (s β x : ℝ) : ℕ := dyadicAbove (9 / 5 * (s * L x) / L x ^ β)

def rangeOK (s α β x : ℝ) (j : ℕ) : Prop :=
  L x ^ α ≤ 3 / 2 * ex s x j ∧ 9 / 5 * ex s x j ≤ L x ^ β

def good (s x : ℝ) : Prop :=
  1 < L x ∧ 0 < s ∧
  (∀ k < nG x, rangeOK s (1 / 10) (1 / 5) x (startIdx s (1 / 5) x + k)) ∧
  (∀ k < nG x, rangeOK s (3 / 10) (2 / 5) x (startIdx s (2 / 5) x + k))

theorem rangeOK_of {s α β x : ℝ} (hL : 1 < L x) (hs : 0 < s) (hT : 28 ≤ T x)
    (hy : 1 ≤ 9 / 5 * (s * L x) / L x ^ β) (hαβ : β = α + 1 / 10) :
    ∀ k < nG x, rangeOK s α β x (startIdx s β x + k) := by
  intro k hk
  have hL0 : 0 < L x := by linarith
  obtain ⟨hy1, hy2⟩ := dyadicAbove_spec hy
  have hT0 : 0 ≤ T x / 20 := by linarith
  have hn : (2 : ℝ) ^ nG x ≤ Real.exp (T x / 20) := by
    calc (2 : ℝ) ^ nG x ≤ Real.exp 1 ^ nG x := by
          gcongr; linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp (nG x) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ Real.exp (T x / 20) := Real.exp_le_exp.mpr (Nat.floor_le hT0)
  have he : (12 / 5 : ℝ) ≤ Real.exp (T x / 20) := by
    linarith [Real.add_one_le_exp (T x / 20)]
  have hN : (2 : ℝ) ^ nG x * L x ^ α * (12 / 5) ≤ L x ^ β := by
    rw [L_rpow hL0, L_rpow hL0]
    calc (2 : ℝ) ^ nG x * Real.exp (T x * α) * (12 / 5) ≤
          Real.exp (T x / 20) * Real.exp (T x * α) * Real.exp (T x / 20) := by gcongr
      _ = Real.exp (T x * β) := by
          rw [← Real.exp_add, ← Real.exp_add, hαβ]; congr 1; ring
  exact range_of (by positivity) (Real.rpow_pos_of_pos hL0 _) (Real.rpow_pos_of_pos hL0 _)
    rfl hy1 hy2 hN hk

theorem eventually_dyadic_start {c β : ℝ} (hc : 0 < c) (hβ : β < 1) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ c * L x / L x ^ β := by
  have ht : Tendsto (fun x => c * Real.exp ((1 - β) * T x)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (T_tendsto.const_mul_atTop (by linarith))).const_mul_atTop hc
  filter_upwards [ht.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x h1 hL
  have hL0 : 0 < L x := hL
  rw [L_rpow hL0, mul_div_assoc, L_eq_exp hL0, ← Real.exp_sub]
  convert h1 using 3
  ring

theorem eventually_good {s : ℝ} (hs : 0 < s) : ∀ᶠ x : ℝ in atTop, good s x := by
  have hc : 0 < 9 / 5 * s := by positivity
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1,
    T_tendsto.eventually_ge_atTop 28,
    eventually_dyadic_start hc (show (1 / 5 : ℝ) < 1 by norm_num),
    eventually_dyadic_start hc (show (2 / 5 : ℝ) < 1 by norm_num)] with x hL hT hyS hyB
  have hL' : 1 < L x := hL
  refine ⟨hL', hs, rangeOK_of hL' hs hT ?_ (by norm_num),
    rangeOK_of hL' hs hT ?_ (by norm_num)⟩
  · simpa only [mul_assoc] using hyS
  · simpa only [mul_assoc] using hyB

/-! ## The groups -/

def idx (s x : ℝ) (g : Fin (nG x + nG x)) : ℕ :=
  if (g : ℕ) < nG x then startIdx s (1 / 5) x + g else startIdx s (2 / 5) x + (g - nG x)

def smallSet (n : ℕ) : Finset (Fin (n + n)) := Finset.univ.filter fun g => (g : ℕ) < n

theorem mem_smallSet {n : ℕ} {g : Fin (n + n)} : g ∈ smallSet n ↔ (g : ℕ) < n := by
  simp [smallSet]

theorem card_smallSet (n : ℕ) : (smallSet n).card = n := by
  rw [smallSet, Fin.card_filter_val_lt]; omega

theorem card_bigSet (n : ℕ) : (Finset.univ \ smallSet n).card = n := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, card_smallSet]; omega

theorem idx_range {s x : ℝ} (h : good s x) (g : Fin (nG x + nG x)) :
    if (g : ℕ) < nG x then rangeOK s (1 / 10) (1 / 5) x (idx s x g)
    else rangeOK s (3 / 10) (2 / 5) x (idx s x g) := by
  obtain ⟨-, -, hS, hB⟩ := h
  by_cases hg : (g : ℕ) < nG x
  · simp only [hg, ↓reduceIte, idx]; exact hS _ hg
  · simp only [hg, ↓reduceIte, idx]; exact hB _ (by omega)

theorem small_le {s x : ℝ} {j : ℕ} {p : ℕ} (hr : rangeOK s (1 / 10) (1 / 5) x j)
    (hp : p ∈ grp (ex s x j)) : (p : ℝ) ≤ Real.exp (L x ^ (1 / 5 : ℝ)) :=
  (mem_grp.mp hp).2.2.trans (Real.exp_le_exp.mpr hr.2)

theorem big_gt {s x : ℝ} {j : ℕ} {p : ℕ} (hr : rangeOK s (3 / 10) (2 / 5) x j)
    (hp : p ∈ grp (ex s x j)) : Real.exp (L x ^ (3 / 10 : ℝ)) < p :=
  (Real.exp_le_exp.mpr hr.1).trans_lt (mem_grp.mp hp).2.1

theorem grp_disjoint' {s x : ℝ} (hu : 0 < s * L x) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (grp (ex s x i)) (grp (ex s x j)) :=
  grp_disjoint hu hij

theorem mixed_disjoint {s x : ℝ} (hL : 1 < L x) {i j : ℕ}
    (hi : rangeOK s (1 / 10) (1 / 5) x i) (hj : rangeOK s (3 / 10) (2 / 5) x j) :
    Disjoint (grp (ex s x i)) (grp (ex s x j)) := by
  refine Finset.disjoint_left.mpr fun p hpi hpj => ?_
  have h1 := small_le hi hpi
  have h2 := big_gt hj hpj
  have h3 : Real.exp (L x ^ (1 / 5 : ℝ)) < Real.exp (L x ^ (3 / 10 : ℝ)) :=
    Real.exp_lt_exp.mpr (Real.rpow_lt_rpow_of_exponent_lt hL (by norm_num))
  linarith

def mkGroups (s x : ℝ) (h : good s x) : PrimeGroups where
  size := nG x + nG x
  primes g := grp (ex s x (idx s x g))
  small := smallSet (nG x)
  prime g p hp := (mem_grp.mp hp).1
  disjoint g g' hgg' := by
    have hL : 1 < L x := h.1
    have hu : 0 < s * L x := mul_pos h.2.1 (by linarith)
    have rg := idx_range h g
    have rg' := idx_range h g'
    have hne : (g : ℕ) ≠ g' := fun e => hgg' (Fin.ext e)
    by_cases hg : (g : ℕ) < nG x <;> by_cases hg' : (g' : ℕ) < nG x <;>
      simp only [hg, hg', ↓reduceIte] at rg rg'
    · apply grp_disjoint' hu
      simp only [idx, hg, hg', ↓reduceIte]; omega
    · exact mixed_disjoint hL rg rg'
    · exact (mixed_disjoint hL rg' rg).symm
    · apply grp_disjoint' hu
      simp only [idx, hg, hg', ↓reduceIte]; omega

def emptyGroups : PrimeGroups where
  size := 0
  primes := Fin.elim0
  small := ∅
  prime g := g.elim0
  disjoint g := g.elim0

def groups (s x : ℝ) : PrimeGroups :=
  if h : good s x then mkGroups s x h else emptyGroups

theorem groups_eq {s x : ℝ} (h : good s x) : groups s x = mkGroups s x h := by
  simp only [groups, h, ↓reduceDIte]

end Erdos821.P7Band
