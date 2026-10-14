import Erdos821.S10.BalancedTasks

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S10Brough

open Erdos821.Blueprint Erdos821.P10 Erdos821.P7Core Erdos821.Blueprint.Analytic
attribute [local instance] Classical.propDecidable

/-- The two logarithmic product indices differ by an absolute constant. -/
theorem natLog_five_floor_gap (x : ℝ) (hx : 5 ≤ x) :
    Nat.log 2 ⌊5 * x⌋₊ ≤ Nat.log 2 ⌊x⌋₊ + 4 := by
  have hxpos : 0 < x := by linarith
  have hfloorxpos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hfloor5pos : 0 < ⌊5 * x⌋₊ := Nat.floor_pos.mpr (by nlinarith [hx])
  have hxlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hfloorlower : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    nlinarith
  have hfloor5le : (⌊5 * x⌋₊ : ℝ) ≤ 5 * x := Nat.floor_le (by positivity)
  have hratio : ⌊5 * x⌋₊ ≤ 16 * ⌊x⌋₊ := by
    have hcast : (⌊5 * x⌋₊ : ℝ) ≤ 16 * (⌊x⌋₊ : ℝ) := by nlinarith
    exact_mod_cast hcast
  have hpow : ⌊x⌋₊ < 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hpow' : ⌊5 * x⌋₊ < 2 ^ (Nat.log 2 ⌊x⌋₊ + 5) := by
    calc
      ⌊5 * x⌋₊ ≤ 16 * ⌊x⌋₊ := hratio
      _ < 16 * 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) :=
        Nat.mul_lt_mul_of_pos_left hpow (by norm_num)
      _ = 2 ^ (Nat.log 2 ⌊x⌋₊ + 5) := by ring
  have hlog := Nat.log_lt_of_lt_pow hfloor5pos.ne' hpow'
  omega


/-- The balanced interval meets at most `O(κ log x + 1)` natural dyadic blocks. -/
theorem balanced_dyadic_index_count (x κ : ℝ) (hx : 1 < x)
    (hκ : 0 < κ) (hκ' : κ < 1 / 50)
    (hgap : 2 * x ^ (1 / 2 - 2 * κ) ≤ x ^ (1 / 2 + 2 * κ)) :
    ((Finset.Icc (Nat.log 2 ⌈x ^ (1 / 2 - 2 * κ)⌉₊)
        (Nat.log 2 ⌊x ^ (1 / 2 + 2 * κ)⌋₊)).card : ℝ) ≤
      8 * (κ * Analytic.L x + 1) := by
  let a : ℝ := 1 / 2 - 2 * κ
  let b : ℝ := 1 / 2 + 2 * κ
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hb : 0 < b := by dsimp [b]; nlinarith
  have hxa : 1 < x ^ a := Real.one_lt_rpow hx ha
  have hxb : 1 < x ^ b := Real.one_lt_rpow hx hb
  have hceilpos : 0 < ⌈x ^ a⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hfloorpos : 0 < ⌊x ^ b⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hceil_le_xb : (⌈x ^ a⌉₊ : ℝ) ≤ x ^ b := by
    calc
      (⌈x ^ a⌉₊ : ℝ) ≤ x ^ a + 1 :=
        (Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith : 0 ≤ x) a)).le
      _ ≤ 2 * x ^ a := by nlinarith [Real.rpow_pos_of_pos (by linarith : 0 < x) a]
      _ ≤ x ^ b := by simpa [a, b] using hgap
  have hceil_le_floor : ⌈x ^ a⌉₊ ≤ ⌊x ^ b⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg (by linarith : 0 ≤ x) b)).2 hceil_le_xb
  let klo := Nat.log 2 ⌈x ^ a⌉₊
  let khi := Nat.log 2 ⌊x ^ b⌋₊
  have hkl : klo ≤ khi := Nat.log_mono_right hceil_le_floor
  have hlog2 : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogklo : a * Real.log x < (klo : ℝ) * Real.log 2 + Real.log 2 := by
    have hpowNat : ⌈x ^ a⌉₊ < 2 ^ (klo + 1) := by
      dsimp [klo]
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hpowReal : (⌈x ^ a⌉₊ : ℝ) < (2 : ℝ) ^ (klo + 1) := by
      exact_mod_cast hpowNat
    have hlog := Real.log_lt_log (Real.rpow_pos_of_pos (by linarith : 0 < x) a)
      (lt_of_le_of_lt (Nat.le_ceil _) hpowReal)
    rw [Real.log_rpow (by linarith : 0 < x), Real.log_pow] at hlog
    have hcast : ((klo + 1 : ℕ) : ℝ) = (klo : ℝ) + 1 := by norm_num
    rw [hcast] at hlog
    calc
      a * Real.log x < ((klo : ℝ) + 1) * Real.log 2 := hlog
      _ = (klo : ℝ) * Real.log 2 + Real.log 2 := by ring
  have hlogkhi : (khi : ℝ) * Real.log 2 ≤ b * Real.log x := by
    have hpowNat : 2 ^ khi ≤ ⌊x ^ b⌋₊ := Nat.pow_log_le_self 2 hfloorpos.ne'
    have hpowReal : (2 : ℝ) ^ khi ≤ x ^ b := by
      calc
        (2 : ℝ) ^ khi = ((2 ^ khi : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ ⌊x ^ b⌋₊ := by exact_mod_cast hpowNat
        _ ≤ x ^ b := Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ x) b)
    have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ khi) hpowReal
    rw [Real.log_pow, Real.log_rpow (by linarith : 0 < x)] at hlog
    simpa [b] using hlog
  have hcard :
      ((Finset.Icc klo khi).card : ℝ) = ((khi - klo : ℕ) : ℝ) + 1 := by
    rw [Nat.card_Icc]
    exact_mod_cast (show khi + 1 - klo = (khi - klo) + 1 by omega)
  have hdiff :
      (((khi - klo : ℕ) : ℝ) + 1) * Real.log 2 <
        4 * κ * Real.log x + 2 * Real.log 2 := by
    have hcast : ((khi - klo : ℕ) : ℝ) = (khi : ℝ) - (klo : ℝ) := by
      exact Nat.cast_sub hkl
    rw [hcast]
    dsimp [a, b] at hlogklo hlogkhi
    nlinarith [hlogklo, hlogkhi]
  have hratioA :
      ((Finset.Icc klo khi).card : ℝ) ≤
        (4 * κ * Real.log x + 2 * Real.log 2) / Real.log 2 := by
    rw [hcard]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    nlinarith [hdiff]
  have hratio :
      ((Finset.Icc klo khi).card : ℝ) ≤ (4 / Real.log 2) * (κ * Real.log x) + 2 := by
    calc
      ((Finset.Icc klo khi).card : ℝ) ≤
          (4 * κ * Real.log x + 2 * Real.log 2) / Real.log 2 := hratioA
      _ = (4 / Real.log 2) * (κ * Real.log x) + 2 := by
        field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hcoef : 4 / Real.log 2 ≤ 8 := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    nlinarith
  have hLnonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hκL : 0 ≤ κ * Real.log x := mul_nonneg hκ.le hLnonneg
  calc
    ((Finset.Icc klo khi).card : ℝ) ≤ (4 / Real.log 2) * (κ * Real.log x) + 2 := hratio
    _ ≤ 8 * (κ * Real.log x) + 8 := by nlinarith
    _ = 8 * (κ * Analytic.L x + 1) := by simp [Analytic.L]; ring

def roughPairCore (C : CandidateData) (x : ℝ) (jstar m n : ℕ) : ℝ :=
  if Odd (m * n) ∧ 1 < m * n then
    C.weighted x jstar ((m * n - 1) / 2) else 0

def roughWindowPairTerm (C : CandidateData) (x : ℝ) (jstar m n : ℕ) : ℝ :=
  if Odd (m * n) ∧ 1 < m * n then
    C.weighted x jstar ((m * n - 1) / 2) *
      (if rough (Analytic.W x) m then 1 else 0) *
        (if rough (Analytic.W x) n then 1 else 0)
  else 0

theorem balancedRoughWindowMass_eq_sum (C : CandidateData) (x : ℝ)
    (jstar : ℕ) (κ : ℝ) :
    balancedRoughWindowMass C x jstar κ =
      ∑ z ∈ balancedWindow x κ ×ˢ balancedWindow x κ,
        roughWindowPairTerm C x jstar z.1 z.2 := by
  unfold balancedRoughWindowMass balancedPairWindowMass roughWindowPairTerm
  rw [← Finset.sum_product']

theorem balancedRoughWindowMass_eq_nonzero_sum (C : CandidateData) (x : ℝ)
    (jstar : ℕ) (κ : ℝ) :
    balancedRoughWindowMass C x jstar κ =
      ∑ z ∈ (balancedWindow x κ ×ˢ balancedWindow x κ).filter
          (fun z => roughWindowPairTerm C x jstar z.1 z.2 ≠ 0),
        roughWindowPairTerm C x jstar z.1 z.2 := by
  rw [balancedRoughWindowMass_eq_sum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨hz, hne⟩)

theorem roughWindowPairTerm_ne_zero_data (C : CandidateData) (x : ℝ)
    (jstar : ℕ) (m n : ℕ)
    (hterm : roughWindowPairTerm C x jstar m n ≠ 0) :
    Odd (m * n) ∧ 1 < m * n ∧
      rough (Analytic.W x) m ∧ rough (Analytic.W x) n ∧
      C.weighted x jstar ((m * n - 1) / 2) ≠ 0 := by
  unfold roughWindowPairTerm at hterm
  by_cases hcond : Odd (m * n) ∧ 1 < m * n
  · simp only [if_pos hcond] at hterm
    rcases hcond with ⟨hodd, hgt⟩
    have hmrough : rough (Analytic.W x) m := by
      by_contra hm
      simp [hm] at hterm
    have hnrough : rough (Analytic.W x) n := by
      by_contra hn
      simp [hn] at hterm
    have hweight : C.weighted x jstar ((m * n - 1) / 2) ≠ 0 := by
      intro hw
      simp [hw, hmrough, hnrough] at hterm
    exact ⟨hodd, hgt, hmrough, hnrough, hweight⟩
  · simp [hcond] at hterm

theorem balancedRoughSum_eq_pair (C : CandidateData) (x M N : ℝ)
    (jstar : ℕ) :
    balancedRoughSum C x M N jstar =
      ∑ z ∈ ((Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊).filter (rough (Analytic.W x)) ×ˢ
          (Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊).filter (rough (Analytic.W x))),
        roughPairCore C x jstar z.1 z.2 := by
  unfold balancedRoughSum roughPairCore
  rw [← Finset.sum_product']

theorem supported_pair_index_sum_bounds (C : CandidateData) (x : ℝ)
    (jstar m n k l : ℕ) (hx : 5 ≤ x)
    (hodd : Odd (m * n))
    (hweight : C.weighted x jstar ((m * n - 1) / 2) ≠ 0)
    (hsupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hmBlock : m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)))
    (hnBlock : n ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1))) :
    Nat.log 2 ⌊x⌋₊ ≤ k + l ∧ k + l ≤ Nat.log 2 ⌊5 * x⌋₊ := by
  have hfloorxpos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hfloor5pos : 0 < ⌊5 * x⌋₊ := Nat.floor_pos.mpr (by nlinarith [hx])
  have hmul : m * n = 2 * ((m * n - 1) / 2) + 1 := by
    rcases hodd with ⟨q, hq⟩
    rw [hq]
    omega
  have hmulReal : (m * n : ℕ) = 2 * (((m * n - 1) / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hmul
  have hmulReal' : (m : ℝ) * (n : ℝ) =
      2 * (((m * n - 1) / 2 : ℕ) : ℝ) + 1 := by
    simpa only [Nat.cast_mul] using hmulReal
  have huSupport := hsupport ((m * n - 1) / 2) hweight
  have hprodLo : 2 * x ≤ (m * n : ℝ) := by nlinarith [huSupport.1, hmulReal']
  have hprodHi : (m * n : ℝ) ≤ 5 * x := by
    have hfour : (m * n : ℝ) ≤ 4 * x + 1 := by nlinarith [huSupport.2, hmulReal']
    nlinarith [hfour, hx]
  rcases Finset.mem_Ico.mp hmBlock with ⟨hmlo, hmhi⟩
  rcases Finset.mem_Ico.mp hnBlock with ⟨hnlo, hnhi⟩
  have hpowLo : 2 ^ (k + l) ≤ m * n := by
    rw [pow_add]
    exact Nat.mul_le_mul hmlo hnlo
  have hmpos : 0 < m := by
    have hpowpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
    omega
  have hnpos : 0 < n := by
    have hpowpos : 0 < 2 ^ l := Nat.pow_pos (by norm_num)
    omega
  have hpowHi : m * n < 2 ^ (k + l + 2) := by
    calc
      m * n < 2 ^ (k + 1) * n := Nat.mul_lt_mul_of_pos_right hmhi hnpos
      _ ≤ 2 ^ (k + 1) * 2 ^ (l + 1) := Nat.mul_le_mul_left _ hnhi.le
      _ = 2 ^ (k + l + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hpowLoReal : ((2 ^ (k + l) : ℕ) : ℝ) ≤ (m * n : ℝ) := by
    exact_mod_cast hpowLo
  have hpowLoFloor : 2 ^ (k + l) ≤ ⌊5 * x⌋₊ :=
    (Nat.le_floor_iff (by positivity : 0 ≤ 5 * x)).2 (hpowLoReal.trans hprodHi)
  have hsumHi : k + l ≤ Nat.log 2 ⌊5 * x⌋₊ :=
    Nat.le_log_of_pow_le (by norm_num) hpowLoFloor
  have hpowHiReal : (m * n : ℝ) < ((2 ^ (k + l + 2) : ℕ) : ℝ) := by
    exact_mod_cast hpowHi
  have hpowHiFactor :
      ((2 ^ (k + l + 2) : ℕ) : ℝ) = 2 * ((2 ^ (k + l + 1) : ℕ) : ℝ) := by
    have hnat : 2 ^ (k + l + 2) = 2 * 2 ^ (k + l + 1) := by
      rw [show k + l + 2 = (k + l + 1) + 1 by omega, pow_succ]
      simp [Nat.mul_comm]
    exact_mod_cast hnat
  have hxPow : x < ((2 ^ (k + l + 1) : ℕ) : ℝ) := by
    rw [hpowHiFactor] at hpowHiReal
    nlinarith [hprodLo]
  have hfloorxltReal : (⌊x⌋₊ : ℝ) < ((2 ^ (k + l + 1) : ℕ) : ℝ) :=
    lt_of_le_of_lt (Nat.floor_le (by linarith)) hxPow
  have hfloorxlt : ⌊x⌋₊ < 2 ^ (k + l + 1) := by exact_mod_cast hfloorxltReal
  have hsumLo : Nat.log 2 ⌊x⌋₊ < k + l + 1 :=
    Nat.log_lt_of_lt_pow hfloorxpos.ne' hfloorxlt
  omega

theorem balanced_dyadic_base_range (x κ : ℝ) (k : ℕ)
    (hx : 1 < x) (hκ : 0 < κ) (hκ' : κ < 1 / 50)
    (hmargin : 2 * x ^ (0.46 : ℝ) ≤ x ^ (1 / 2 - 2 * κ))
    (hk : k ∈ Finset.Icc
      (Nat.log 2 ⌈x ^ (1 / 2 - 2 * κ)⌉₊)
      (Nat.log 2 ⌊x ^ (1 / 2 + 2 * κ)⌋₊)) :
    x ^ (0.46 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) ∧
      ((2 ^ k : ℕ) : ℝ) ≤ x ^ (0.54 : ℝ) := by
  let a : ℝ := 1 / 2 - 2 * κ
  let b : ℝ := 1 / 2 + 2 * κ
  rcases Finset.mem_Icc.mp hk with ⟨hklo, hkhi⟩
  have hceilPos : 0 < ⌈x ^ a⌉₊ :=
    Nat.ceil_pos.mpr (by
      have ha : 0 < a := by dsimp [a]; nlinarith [hκ']
      exact lt_trans (by norm_num) (Real.one_lt_rpow hx ha))
  have hfloorPos : 0 < ⌊x ^ b⌋₊ :=
    Nat.floor_pos.mpr (by
      have hb : 0 < b := by dsimp [b]; nlinarith [hκ]
      exact (Real.one_lt_rpow hx hb).le)
  have hloNat : 2 ^ (Nat.log 2 ⌈x ^ a⌉₊) ≤ 2 ^ k :=
    pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hklo
  have hceilLt : ⌈x ^ a⌉₊ < 2 ^ (Nat.log 2 ⌈x ^ a⌉₊ + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hpowSucc :
      ((2 ^ (Nat.log 2 ⌈x ^ a⌉₊ + 1) : ℕ) : ℝ) =
        2 * ((2 ^ Nat.log 2 ⌈x ^ a⌉₊ : ℕ) : ℝ) := by
    have hnat : 2 ^ (Nat.log 2 ⌈x ^ a⌉₊ + 1) =
        2 * 2 ^ Nat.log 2 ⌈x ^ a⌉₊ := by
      rw [pow_succ]
      simp [Nat.mul_comm]
    exact_mod_cast hnat
  have hceilLtReal : (⌈x ^ a⌉₊ : ℝ) <
      2 * ((2 ^ Nat.log 2 ⌈x ^ a⌉₊ : ℕ) : ℝ) := by
    have hcast : (⌈x ^ a⌉₊ : ℝ) <
        ((2 ^ (Nat.log 2 ⌈x ^ a⌉₊ + 1) : ℕ) : ℝ) := by exact_mod_cast hceilLt
    rw [hpowSucc] at hcast
    exact hcast
  have hpowlo : x ^ a < 2 * ((2 ^ k : ℕ) : ℝ) := by
    have hceilLower : x ^ a ≤ (⌈x ^ a⌉₊ : ℝ) := Nat.le_ceil _
    have hpowcast : ((2 ^ Nat.log 2 ⌈x ^ a⌉₊ : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast hloNat
    calc
      x ^ a ≤ (⌈x ^ a⌉₊ : ℝ) := hceilLower
      _ < 2 * ((2 ^ Nat.log 2 ⌈x ^ a⌉₊ : ℕ) : ℝ) := hceilLtReal
      _ ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by gcongr
  have hlo : x ^ (0.46 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    nlinarith [hmargin, hpowlo, Real.rpow_pos_of_pos (by linarith : 0 < x) (0.46 : ℝ)]
  have hpowNatHi : 2 ^ k ≤ ⌊x ^ b⌋₊ := by
    exact (pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hkhi).trans
      (Nat.pow_log_le_self 2 hfloorPos.ne')
  have hpowRealHi : ((2 ^ k : ℕ) : ℝ) ≤ x ^ b := by
    have hcast : ((2 ^ k : ℕ) : ℝ) ≤ (⌊x ^ b⌋₊ : ℝ) := by exact_mod_cast hpowNatHi
    exact hcast.trans (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ x) b))
  have hb54 : b ≤ (0.54 : ℝ) := by dsimp [b]; nlinarith [hκ']
  have hhi : ((2 ^ k : ℕ) : ℝ) ≤ x ^ (0.54 : ℝ) :=
    hpowRealHi.trans (Real.rpow_le_rpow_of_exponent_le hx.le hb54)
  exact ⟨hlo, hhi⟩

def balancedDyadicActivePairs (klo khi slo shi : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc klo khi ×ˢ Finset.Icc klo khi).filter
    (fun p => p.1 + p.2 ∈ Finset.Icc slo shi)

theorem balancedDyadicActivePairs_card_le (klo khi slo shi : ℕ)
    (hwidth : shi ≤ slo + 4) :
    ((balancedDyadicActivePairs klo khi slo shi).card : ℝ) ≤
      5 * (Finset.Icc klo khi).card := by
  classical
  let I := Finset.Icc klo khi
  let A := I ×ˢ Finset.Icc 0 4
  let φ : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, slo + p.2 - p.1)
  have hsub : balancedDyadicActivePairs klo khi slo shi ⊆ A.image φ := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp', hpSum⟩
    rcases Finset.mem_product.mp hp' with ⟨hpk, hpl⟩
    rcases Finset.mem_Icc.mp hpSum with ⟨hslo, hshi⟩
    let d := p.1 + p.2 - slo
    have hdhi : d ≤ 4 := by dsimp [d]; omega
    have hmap : φ (p.1, d) = p := by
      apply Prod.ext
      · rfl
      · dsimp [φ, d]
        omega
    apply Finset.mem_image.mpr
    refine ⟨(p.1, d), Finset.mem_product.mpr ⟨?_, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hdhi⟩⟩, hmap⟩
    simpa [I] using hpk
  have hcard : (balancedDyadicActivePairs klo khi slo shi).card ≤ I.card * 5 := by
    calc
      (balancedDyadicActivePairs klo khi slo shi).card ≤ (A.image φ).card := Finset.card_le_card hsub
      _ ≤ A.card := Finset.card_image_le
      _ = I.card * 5 := by simp [A]
  have hcardReal :
      ((balancedDyadicActivePairs klo khi slo shi).card : ℝ) ≤ (I.card : ℝ) * 5 := by
    exact_mod_cast hcard
  change ((balancedDyadicActivePairs klo khi slo shi).card : ℝ) ≤ 5 * (I.card : ℝ)
  nlinarith [hcardReal]

theorem BalancedWindowRoughTask_proof : BalancedWindowRoughTask := by
  intro hc δ C hGeometry hBounds hRough
  obtain ⟨Kp, hKp, hP9⟩ := hRough
  obtain ⟨Kc, CA, cmin, cmax, hKc, hcmin, hcmax, hBoundsEventual⟩ := hBounds
  refine ⟨40 * Kp, by positivity, ?_⟩
  intro κ hκ hκ' jstar hjstar
  have hP9Eventual := hP9 jstar hjstar
  have hBoundsEventual' := hBoundsEventual jstar hjstar
  have hgapEventual : ∀ᶠ x : ℝ in atTop,
      2 * x ^ (1 / 2 - 2 * κ) ≤ x ^ (1 / 2 + 2 * κ) := by
    have hpow := (tendsto_rpow_atTop (show 0 < 4 * κ by positivity)).eventually
      (eventually_ge_atTop (2 : ℝ))
    filter_upwards [hpow, eventually_gt_atTop (1 : ℝ)] with x hpow hx
    have hxpos : 0 < x := by linarith
    have heq : x ^ (1 / 2 + 2 * κ) =
        x ^ (1 / 2 - 2 * κ) * x ^ (4 * κ) := by
      rw [show 1 / 2 + 2 * κ = (1 / 2 - 2 * κ) + 4 * κ by ring,
        Real.rpow_add hxpos]
    calc
      2 * x ^ (1 / 2 - 2 * κ) = x ^ (1 / 2 - 2 * κ) * 2 := by ring
      _ ≤ x ^ (1 / 2 - 2 * κ) * x ^ (4 * κ) :=
        mul_le_mul_of_nonneg_left hpow
          (Real.rpow_nonneg hxpos.le (1 / 2 - 2 * κ))
      _ = x ^ (1 / 2 + 2 * κ) := heq.symm
  have hmarginEventual : ∀ᶠ x : ℝ in atTop,
      2 * x ^ (0.46 : ℝ) ≤ x ^ (1 / 2 - 2 * κ) := by
    have hdelta : 0 < (1 / 2 - 2 * κ) - (0.46 : ℝ) := by
      norm_num
      nlinarith [hκ']
    have hpow := (tendsto_rpow_atTop hdelta).eventually
      (eventually_ge_atTop (2 : ℝ))
    filter_upwards [hpow, eventually_gt_atTop (1 : ℝ)] with x hpow hx
    have hxpos : 0 < x := by linarith
    have heq : x ^ (1 / 2 - 2 * κ) =
        x ^ (0.46 : ℝ) * x ^ ((1 / 2 - 2 * κ) - (0.46 : ℝ)) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    calc
      2 * x ^ (0.46 : ℝ) = x ^ (0.46 : ℝ) * 2 := by ring
      _ ≤ x ^ (0.46 : ℝ) * x ^ ((1 / 2 - 2 * κ) - (0.46 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow
          (Real.rpow_nonneg hxpos.le (0.46 : ℝ))
      _ = x ^ (1 / 2 - 2 * κ) := heq.symm
  filter_upwards [hP9Eventual, hBoundsEventual', hgapEventual,
    hmarginEventual, eventually_ge_atTop (5 : ℝ)] with x hP9x hBoundsx hgapx hmarginx hx5
  rcases hBoundsx with ⟨_, _, _, hWeightNonneg, _, hSupport⟩
  have hSupport' : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x := by
    intro u hu
    rcases hSupport u hu with ⟨hlo, hhi, _⟩
    exact ⟨hlo, hhi⟩
  have hmassNonneg : 0 ≤ C.mass x jstar := by
    unfold CandidateData.mass
    apply Finset.sum_nonneg
    intro u hu
    exact hWeightNonneg u
  have hboxNonneg : 0 ≤ Kp * C.mass x jstar * sieveProduct (Analytic.W x) ^ 2 := by
    positivity
  let klo := Nat.log 2 ⌈x ^ (1 / 2 - 2 * κ)⌉₊
  let khi := Nat.log 2 ⌊x ^ (1 / 2 + 2 * κ)⌋₊
  let slo := Nat.log 2 ⌊x⌋₊
  let shi := Nat.log 2 ⌊5 * x⌋₊
  let I := Finset.Icc klo khi
  let T := balancedDyadicActivePairs klo khi slo shi
  let S := (balancedWindow x κ ×ˢ balancedWindow x κ).filter
    (fun z => roughWindowPairTerm C x jstar z.1 z.2 ≠ 0)
  let g : ℕ × ℕ → ℕ × ℕ := fun z => (Nat.log 2 z.1, Nat.log 2 z.2)
  have hx1 : 1 < x := by linarith
  have hIcount : (I.card : ℝ) ≤ 8 * (κ * Analytic.L x + 1) := by
    dsimp [I, klo, khi]
    exact balanced_dyadic_index_count x κ hx1 hκ hκ' hgapx
  have hsumWidth : shi ≤ slo + 4 := by
    dsimp [shi, slo]
    exact natLog_five_floor_gap x hx5
  have hTcardSmall : (T.card : ℝ) ≤ 5 * (I.card : ℝ) := by
    simpa [T, I] using balancedDyadicActivePairs_card_le klo khi slo shi hsumWidth
  have hTcount : (T.card : ℝ) ≤ 40 * (κ * Analytic.L x + 1) := by
    nlinarith [hTcardSmall, hIcount]
  have hmap : ∀ z ∈ S, g z ∈ T := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzWindow, hterm⟩
    rcases Finset.mem_product.mp hzWindow with ⟨hmWindow, hnWindow⟩
    change z.1 ∈ Finset.Icc _ _ at hmWindow
    change z.2 ∈ Finset.Icc _ _ at hnWindow
    rcases Finset.mem_Icc.mp hmWindow with ⟨hmlo, hmhi⟩
    rcases Finset.mem_Icc.mp hnWindow with ⟨hnlo, hnhi⟩
    rcases roughWindowPairTerm_ne_zero_data C x jstar z.1 z.2 hterm with
      ⟨hodd, _, _, _, hweight⟩
    have hmIndexLo : klo ≤ Nat.log 2 z.1 := by
      dsimp [klo]
      exact Nat.log_mono_right hmlo
    have hmIndexHi : Nat.log 2 z.1 ≤ khi := by
      dsimp [khi]
      exact Nat.log_mono_right hmhi
    have hnIndexLo : klo ≤ Nat.log 2 z.2 := by
      dsimp [klo]
      exact Nat.log_mono_right hnlo
    have hnIndexHi : Nat.log 2 z.2 ≤ khi := by
      dsimp [khi]
      exact Nat.log_mono_right hnhi
    have hodd' : Odd (z.1 * z.2) := hodd
    have hprodpos : 0 < z.1 * z.2 := by
      rcases hodd with ⟨q, hq⟩
      rw [hq]
      omega
    have hmpos : 0 < z.1 := by
      by_contra hm
      have hm0 : z.1 = 0 := by omega
      simp [hm0] at hprodpos
    have hnpos : 0 < z.2 := by
      by_contra hn
      have hn0 : z.2 = 0 := by omega
      simp [hn0] at hprodpos
    have hsum := supported_pair_index_sum_bounds C x jstar z.1 z.2
      (Nat.log 2 z.1) (Nat.log 2 z.2) hx5 hodd' hweight hSupport'
      (mem_nat_dyadicBlock z.1 hmpos) (mem_nat_dyadicBlock z.2 hnpos)
    have hkl : g z ∈ Finset.Icc klo khi ×ˢ Finset.Icc klo khi := by
      dsimp [g]
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hmIndexLo, hmIndexHi⟩,
          Finset.mem_Icc.mpr ⟨hnIndexLo, hnIndexHi⟩⟩
    have hsumMem :
        (Nat.log 2 z.1 + Nat.log 2 z.2) ∈ Finset.Icc slo shi := by
      dsimp [slo, shi]
      exact Finset.mem_Icc.mpr hsum
    apply Finset.mem_filter.mpr
    refine ⟨?_, hsumMem⟩
    simpa [T, balancedDyadicActivePairs, g] using hkl
  have hFiberBound : ∀ p ∈ T,
      (∑ z ∈ S.filter (fun z => g z = p), roughWindowPairTerm C x jstar z.1 z.2) ≤
        Kp * C.mass x jstar * sieveProduct (Analytic.W x) ^ 2 := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpbox, _⟩
    rcases Finset.mem_product.mp hpbox with ⟨hpk, hpl⟩
    have hMRange := balanced_dyadic_base_range x κ p.1 hx1 hκ hκ' hmarginx hpk
    have hNRange := balanced_dyadic_base_range x κ p.2 hx1 hκ hκ' hmarginx hpl
    let M : ℝ := ((2 ^ p.1 : ℕ) : ℝ)
    let N : ℝ := ((2 ^ p.2 : ℕ) : ℝ)
    have hBoxP9 := hP9x M N hMRange.1 hMRange.2 hNRange.1 hNRange.2
    let F := S.filter (fun z => g z = p)
    let B :=
      (Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊).filter (rough (Analytic.W x)) ×ˢ
        (Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊).filter (rough (Analytic.W x))
    have hFsub : F ⊆ B := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzS, hzg⟩
      rcases Finset.mem_filter.mp hzS with ⟨hzWindow, hterm⟩
      rcases roughWindowPairTerm_ne_zero_data C x jstar z.1 z.2 hterm with
        ⟨hodd, _, hrm, hrn, _⟩
      change (Nat.log 2 z.1, Nat.log 2 z.2) = p at hzg
      have hmk : Nat.log 2 z.1 = p.1 := by
        simpa using congrArg (fun q : ℕ × ℕ => q.1) hzg
      have hnk : Nat.log 2 z.2 = p.2 := by
        simpa using congrArg (fun q : ℕ × ℕ => q.2) hzg
      have hprodpos : 0 < z.1 * z.2 := by
        rcases hodd with ⟨q, hq⟩
        rw [hq]
        omega
      have hmpos : 0 < z.1 := by
        by_contra hm
        have hm0 : z.1 = 0 := by omega
        simp [hm0] at hprodpos
      have hnpos : 0 < z.2 := by
        by_contra hn
        have hn0 : z.2 = 0 := by omega
        simp [hn0] at hprodpos
      have hmBlock : z.1 ∈ Finset.Ico (2 ^ p.1) (2 ^ (p.1 + 1)) :=
        (mem_nat_dyadicBlock_iff z.1 p.1 hmpos).2 hmk
      have hnBlock : z.2 ∈ Finset.Ico (2 ^ p.2) (2 ^ (p.2 + 1)) :=
        (mem_nat_dyadicBlock_iff z.2 p.2 hnpos).2 hnk
      have hMBlock : Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊ =
          Finset.Ico (2 ^ p.1) (2 ^ (p.1 + 1)) := by
        dsimp [M]
        have htop : 2 * ((2 ^ p.1 : ℕ) : ℝ) = ((2 ^ (p.1 + 1) : ℕ) : ℝ) := by
          norm_cast
          rw [pow_succ]
          simp [Nat.mul_comm]
        rw [Nat.ceil_natCast, htop, Nat.ceil_natCast]
      have hNBlock : Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊ =
          Finset.Ico (2 ^ p.2) (2 ^ (p.2 + 1)) := by
        dsimp [N]
        have htop : 2 * ((2 ^ p.2 : ℕ) : ℝ) = ((2 ^ (p.2 + 1) : ℕ) : ℝ) := by
          norm_cast
          rw [pow_succ]
          simp [Nat.mul_comm]
        rw [Nat.ceil_natCast, htop, Nat.ceil_natCast]
      refine Finset.mem_product.mpr ?_
      exact ⟨Finset.mem_filter.mpr ⟨by simpa [hMBlock] using hmBlock, hrm⟩,
        Finset.mem_filter.mpr ⟨by simpa [hNBlock] using hnBlock, hrn⟩⟩
    have hFiberEq :
        (∑ z ∈ F, roughWindowPairTerm C x jstar z.1 z.2) =
          ∑ z ∈ F, roughPairCore C x jstar z.1 z.2 := by
      apply Finset.sum_congr rfl
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzS, _⟩
      rcases Finset.mem_filter.mp hzS with ⟨_, hterm⟩
      rcases roughWindowPairTerm_ne_zero_data C x jstar z.1 z.2 hterm with
        ⟨hodd, hgt, hrm, hrn, _⟩
      simp [roughWindowPairTerm, roughPairCore, hodd, hgt, hrm, hrn]
    have hFiberLeBox :
        (∑ z ∈ F, roughPairCore C x jstar z.1 z.2) ≤
          ∑ z ∈ B, roughPairCore C x jstar z.1 z.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hFsub
      intro z hzB hzF
      unfold roughPairCore
      split_ifs with h
      · exact hWeightNonneg _
      · exact le_rfl
    calc
      (∑ z ∈ S.filter (fun z => g z = p), roughWindowPairTerm C x jstar z.1 z.2) =
          ∑ z ∈ F, roughWindowPairTerm C x jstar z.1 z.2 := by rfl
      _ = ∑ z ∈ F, roughPairCore C x jstar z.1 z.2 := hFiberEq
      _ ≤ ∑ z ∈ B, roughPairCore C x jstar z.1 z.2 := hFiberLeBox
      _ = balancedRoughSum C x M N jstar :=
        (balancedRoughSum_eq_pair C x M N jstar).symm
      _ ≤ Kp * C.mass x jstar * sieveProduct (Analytic.W x) ^ 2 := hBoxP9
  have hReindex :
      (∑ z ∈ S, roughWindowPairTerm C x jstar z.1 z.2) =
        ∑ p ∈ T, ∑ z ∈ S.filter (fun z => g z = p),
          roughWindowPairTerm C x jstar z.1 z.2 :=
    (Finset.sum_fiberwise_of_maps_to (g := g) (t := T) hmap
      (fun z => roughWindowPairTerm C x jstar z.1 z.2)).symm
  have hMassEq : balancedRoughWindowMass C x jstar κ =
      ∑ z ∈ S, roughWindowPairTerm C x jstar z.1 z.2 := by
    simpa [S] using balancedRoughWindowMass_eq_nonzero_sum C x jstar κ
  calc
    balancedRoughWindowMass C x jstar κ =
        ∑ z ∈ S, roughWindowPairTerm C x jstar z.1 z.2 := hMassEq
    _ = ∑ p ∈ T, ∑ z ∈ S.filter (fun z => g z = p),
          roughWindowPairTerm C x jstar z.1 z.2 := hReindex
    _ ≤ ∑ p ∈ T, Kp * C.mass x jstar * sieveProduct (Analytic.W x) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact hFiberBound p hp
    _ = (T.card : ℝ) * (Kp * C.mass x jstar * sieveProduct (Analytic.W x) ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 40 * (κ * Analytic.L x + 1) *
          (Kp * C.mass x jstar * sieveProduct (Analytic.W x) ^ 2) :=
        mul_le_mul_of_nonneg_right hTcount hboxNonneg
    _ = (40 * Kp) * (κ * Analytic.L x + 1) * C.mass x jstar *
          sieveProduct (Analytic.W x) ^ 2 := by ring

end Erdos821.S10Brough
