import Erdos821.Blueprint.Classical
import Erdos821.P7.PrimeWindowTask
import OAI.NumberTheory.PrimeGaps.Main

set_option maxHeartbeats 1000000

noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Win
open Erdos821.Blueprint

/-- PNT with A=3, C=1, r=1: prime count tracks `li`. -/
theorem prime_count_li_accuracy (hC : ClassicalInputs) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ y : ℝ in atTop,
      |((primesUpTo y).card : ℝ) - li y| ≤ K * y * Real.log y ^ (-3 : ℝ) := by
  obtain ⟨K, hK, hP⟩ := hC.progressions 3 1 (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hP, Filter.eventually_gt_atTop (Real.exp 1)] with y hy hlarge
  have hc : Nat.Coprime 0 1 := by norm_num
  have hlog : 1 ≤ Real.log y := by
    have : Real.exp 1 ≤ y := hlarge.le
    have hpos : 0 < (Real.exp 1 : ℝ) := Real.exp_pos 1
    have := Real.log_le_log hpos this
    rwa [Real.log_exp] at this
  have hpow : (1 : ℝ) ≤ Real.log y ^ (1 : ℝ) := by
    simpa using hlog
  have h := hy 1 0 (by norm_num) (by simpa using hpow) hc
  simpa [primesUpTo, Nat.mod_one, Nat.totient_one] using h

theorem prime_interval_card_add (Y Z : ℝ) (hYZ : ⌊Y⌋₊ ≤ ⌊Z⌋₊) :
    ((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card + (primesUpTo Y).card =
      (primesUpTo Z).card := by
  unfold primesUpTo
  have hsplit : Finset.Icc 1 ⌊Z⌋₊ =
      Finset.Icc 1 ⌊Y⌋₊ ∪ Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdis : Disjoint
      ((Finset.Icc 1 ⌊Y⌋₊).filter Nat.Prime)
      ((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime) := by
    apply Finset.disjoint_left.mpr
    intro n hn1 hn2
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn1 hn2
    omega
  have hcard := congrArg (fun s : Finset ℕ => (s.filter Nat.Prime).card) hsplit
  rw [Finset.filter_union, Finset.card_union_of_disjoint hdis] at hcard
  omega

theorem li_interval_sub (Y Z : ℝ) (hY : 2 ≤ Y) (hYZ : Y ≤ Z) :
    li Z - li Y = ∫ t : ℝ in Y..Z, (Real.log t)⁻¹ := by
  have hlogcont : ContinuousOn Real.log (Set.Icc (2 : ℝ) Z) :=
    Real.continuousOn_log.mono (by
      intro t ht
      exact ne_of_gt (show 0 < t by linarith [ht.1]))
  have hinvcont : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc (2 : ℝ) Z) :=
    hlogcont.inv₀ (by
      intro t ht
      exact ne_of_gt (Real.log_pos (by linarith [ht.1])))
  have hinvcontY : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc (2 : ℝ) Y) :=
    hinvcont.mono (Set.Icc_subset_Icc le_rfl hYZ)
  have h2Z : (2 : ℝ) ≤ Z := hY.trans hYZ
  unfold li
  exact intervalIntegral.integral_interval_sub_left
    (hinvcont.intervalIntegrable_of_Icc h2Z)
    (hinvcontY.intervalIntegrable_of_Icc hY)

theorem li_interval_upper (Y Z : ℝ) (hY : 2 ≤ Y) (hYZ : Y ≤ Z) :
    li Z - li Y ≤ (Z - Y) / Real.log Y := by
  have h2Z : (2 : ℝ) ≤ Z := hY.trans hYZ
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc (2 : ℝ) Z) := by
    apply (Real.continuousOn_log.mono (by
      intro t ht
      exact ne_of_gt (show 0 < t by linarith [ht.1]))).inv₀
    intro t ht
    exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  have hf : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume Y Z :=
    (hcont.mono (Set.Icc_subset_Icc hY le_rfl)).intervalIntegrable_of_Icc hYZ
  have hg : IntervalIntegrable (fun _ : ℝ => (Real.log Y)⁻¹) volume Y Z := by
    exact continuousOn_const.intervalIntegrable_of_Icc hYZ
  have hmono : (∫ t : ℝ in Y..Z, (Real.log t)⁻¹) ≤
      ∫ t : ℝ in Y..Z, (Real.log Y)⁻¹ := by
    apply intervalIntegral.integral_mono_on hYZ hf hg
    intro t ht
    simpa [one_div] using
      (one_div_le_one_div_of_le (Real.log_pos (by linarith [hY]))
        (Real.log_le_log (by linarith [hY]) ht.1))
  calc
    li Z - li Y = ∫ t : ℝ in Y..Z, (Real.log t)⁻¹ := li_interval_sub Y Z hY hYZ
    _ ≤ ∫ t : ℝ in Y..Z, (Real.log Y)⁻¹ := hmono
    _ = (Z - Y) / Real.log Y := by simp [smul_eq_mul, div_eq_mul_inv]

theorem li_interval_lower (Y Z : ℝ) (hY : 2 ≤ Y) (hYZ : Y ≤ Z) :
    (Z - Y) / Real.log Z ≤ li Z - li Y := by
  have h2Z : (2 : ℝ) ≤ Z := hY.trans hYZ
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc (2 : ℝ) Z) := by
    apply (Real.continuousOn_log.mono (by
      intro t ht
      exact ne_of_gt (show 0 < t by linarith [ht.1]))).inv₀
    intro t ht
    exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  have hf : IntervalIntegrable (fun _ : ℝ => (Real.log Z)⁻¹) volume Y Z := by
    exact continuousOn_const.intervalIntegrable_of_Icc hYZ
  have hg : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume Y Z :=
    (hcont.mono (Set.Icc_subset_Icc hY le_rfl)).intervalIntegrable_of_Icc hYZ
  have hmono :
      ∫ t : ℝ in Y..Z, (Real.log Z)⁻¹ ≤
        ∫ t : ℝ in Y..Z, (Real.log t)⁻¹ := by
    apply intervalIntegral.integral_mono_on hYZ hf hg
    intro t ht
    have htpos : 1 < t := by linarith [hY, ht.1]
    have htpos' : 0 < t := by linarith
    have hlogtpos : 0 < Real.log t := Real.log_pos htpos
    have hlogtZ : Real.log t ≤ Real.log Z := Real.log_le_log htpos' ht.2
    simpa [one_div] using one_div_le_one_div_of_le hlogtpos hlogtZ
  calc
    (Z - Y) / Real.log Z = ∫ t : ℝ in Y..Z, (Real.log Z)⁻¹ := by
      simp [smul_eq_mul, div_eq_mul_inv]
    _ ≤ ∫ t : ℝ in Y..Z, (Real.log t)⁻¹ := hmono
    _ = li Z - li Y := (li_interval_sub Y Z hY hYZ).symm

/-- Rewrite `log ^ (-3:ℝ)` as an inverse cube. -/
theorem rpow_neg_three_eq (t : ℝ) (ht : 0 < Real.log t) :
    Real.log t ^ (-3 : ℝ) = ((Real.log t ^ 3)⁻¹) := by
  have hle : 0 ≤ Real.log t := ht.le
  have h3 : (-3 : ℝ) = -((3 : ℕ) : ℝ) := by norm_num
  rw [h3, Real.rpow_neg hle, Real.rpow_natCast]

theorem rpow_neg_three_pos (t : ℝ) (ht : 0 < Real.log t) :
    0 < Real.log t ^ (-3 : ℝ) := by
  exact Real.rpow_pos_of_pos ht _

/-- The closed ceil/floor window contains the half-open floor window. -/
theorem ioc_subset_icc_window (Y Z : ℝ) :
    Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊ ⊆ Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊ := by
  intro n hn
  simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
  obtain ⟨hlo, hhi⟩ := hn
  have hYlt : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hfloor_lt : ⌊Y⌋₊ + 1 ≤ n := Nat.succ_le_of_lt hlo
  have hfloor_real : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfloor_lt
  simp only [Nat.cast_add, Nat.cast_one] at hfloor_real
  have hYn : Y ≤ (n : ℝ) := le_trans hYlt.le hfloor_real
  have hceil : ⌈Y⌉₊ ≤ n := Nat.ceil_le.mpr hYn
  exact ⟨hceil, hhi⟩

theorem filtered_ioc_subset_icc (Y Z : ℝ) :
    (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime ⊆
      (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime :=
  Finset.filter_subset_filter _ (ioc_subset_icc_window Y Z)

/-- Primes in the closed window are bounded above by `Z` once floors cooperate. -/
theorem prime_mem_upper_of_mem_icc (Z : ℝ) (hZ : 0 ≤ Z) (n : ℕ)
    (hn : n ∈ (Finset.Icc ⌈Z⌉₊ ⌊Z⌋₊).filter Nat.Prime) :
    (n : ℝ) ≤ Z := by
  have hmem := (Finset.mem_filter.mp hn).1
  simp only [Finset.mem_Icc] at hmem
  have hle : (n : ℝ) ≤ (⌊Z⌋₊ : ℝ) := by exact_mod_cast hmem.2
  exact hle.trans (Nat.floor_le hZ)

theorem prime_le_of_mem_window (Y Z : ℝ) (hZ : 0 ≤ Z) (n : ℕ)
    (hn : n ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime) :
    (n : ℝ) ≤ Z := by
  have hmem := (Finset.mem_filter.mp hn).1
  simp only [Finset.mem_Icc] at hmem
  have hle : (n : ℝ) ≤ (⌊Z⌋₊ : ℝ) := by exact_mod_cast hmem.2
  exact hle.trans (Nat.floor_le hZ)

theorem prime_ge_of_mem_window (Y Z : ℝ) (n : ℕ)
    (hn : n ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime) :
    Y ≤ (n : ℝ) := by
  have hmem := (Finset.mem_filter.mp hn).1
  simp only [Finset.mem_Icc] at hmem
  have hle : (⌈Y⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmem.1
  exact (Nat.le_ceil Y).trans hle

theorem prime_pos_of_mem (n : ℕ) (hn : n.Prime) : (0 : ℝ) < (n : ℝ) := by
  have h2 : 2 ≤ n := hn.two_le
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  linarith

/-- Lower reciprocal sum via the uniform upper bound `p ≤ Z`. -/
theorem window_sum_ge_card_div (Y Z : ℝ) (hZ : 0 < Z) :
    (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) / Z ≤
      ∑ p ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
  have hsub := filtered_ioc_subset_icc Y Z
  have hnn : ∀ p ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime, (0 : ℝ) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2
    exact inv_nonneg.mpr (prime_pos_of_mem p hprime).le
  have hmono : ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ≤
      ∑ p ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnn p hp)
  have hlower : (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) / Z ≤
      ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
    have hcard := Finset.card_nsmul_le_sum
      (s := (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime)
      (f := fun p : ℕ => (p : ℝ)⁻¹) (n := Z⁻¹)
      (h := by
        intro p hp
        have hprime := (Finset.mem_filter.mp hp).2
        have hmem := (Finset.mem_filter.mp hp).1
        simp only [Finset.mem_Ioc] at hmem
        have hle : (p : ℝ) ≤ (⌊Z⌋₊ : ℝ) := by exact_mod_cast hmem.2
        have hpZ : (p : ℝ) ≤ Z := hle.trans (Nat.floor_le hZ.le)
        have hppos := prime_pos_of_mem p hprime
        exact (inv_le_inv₀ hZ hppos).mpr hpZ)
    simpa [nsmul_eq_mul, div_eq_mul_inv, mul_comm] using hcard
  exact hlower.trans hmono

/-- Upper reciprocal sum via the uniform lower bound `Y ≤ p`. -/
theorem window_sum_le_card_div (Y Z : ℝ) (hY : 0 < Y) :
    ∑ p ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ≤
      (((Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) / Y := by
  have hcard := Finset.sum_le_card_nsmul
    (s := (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime)
    (f := fun p : ℕ => (p : ℝ)⁻¹) (n := Y⁻¹)
    (h := by
      intro p hp
      have hprime := (Finset.mem_filter.mp hp).2
      have hpY := prime_ge_of_mem_window Y Z p hp
      have hppos := prime_pos_of_mem p hprime
      exact (inv_le_inv₀ hppos hY).mpr hpY)
  simpa [nsmul_eq_mul, div_eq_mul_inv, mul_comm] using hcard

/-- Closed-window count is bounded by the total prime count up to `Z`. -/
theorem icc_card_le_primesUpTo (Y Z : ℝ) (hY1 : 1 ≤ ⌈Y⌉₊) :
    ((Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime).card ≤ (primesUpTo Z).card := by
  unfold primesUpTo
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro n hn
  simp only [Finset.mem_Icc] at hn ⊢
  exact ⟨hY1.trans hn.1, hn.2⟩

theorem interval_card_eq (Y Z : ℝ) (hYZ : Y ≤ Z) :
    (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) =
      ((primesUpTo Z).card : ℝ) - ((primesUpTo Y).card : ℝ) := by
  have h := prime_interval_card_add Y Z (Nat.floor_mono hYZ)
  have hcast : ((((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℕ) : ℝ) +
      (((primesUpTo Y).card : ℕ) : ℝ) = (((primesUpTo Z).card : ℕ) : ℝ) := by
    exact_mod_cast h
  linarith

theorem interval_card_lower (Y Z eY eZ : ℝ)
    (hYZ : Y ≤ Z)
    (hYerr : |(((primesUpTo Y).card : ℝ) - li Y)| ≤ eY)
    (hZerr : |(((primesUpTo Z).card : ℝ) - li Z)| ≤ eZ) :
    li Z - li Y - eZ - eY ≤
      (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) := by
  have heq := interval_card_eq Y Z hYZ
  have hY := (abs_le.mp hYerr).2
  have hZ := (abs_le.mp hZerr).1
  linarith

theorem interval_card_upper (Y Z eY eZ : ℝ)
    (hYZ : Y ≤ Z)
    (hYerr : |(((primesUpTo Y).card : ℝ) - li Y)| ≤ eY)
    (hZerr : |(((primesUpTo Z).card : ℝ) - li Z)| ≤ eZ) :
    (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) ≤
      li Z - li Y + eZ + eY := by
  have heq := interval_card_eq Y Z hYZ
  have hY := (abs_le.mp hYerr).1
  have hZ := (abs_le.mp hZerr).2
  linarith

/-- `0.5 ≤ log 2`, from `exp(0.5) < 2`. -/
theorem half_le_log_two : (0.5 : ℝ) ≤ Real.log 2 := by
  have hexp1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp_half_sq : (Real.exp 0.5) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hexp_half_lt : Real.exp 0.5 < 2 := by
    have h1 : (Real.exp 0.5) ^ 2 < (2 : ℝ) ^ 2 := by
      rw [hexp_half_sq]
      norm_num
      linarith [hexp1]
    have hnn1 : (0 : ℝ) ≤ Real.exp 0.5 := (Real.exp_pos _).le
    have hnn2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    exact (sq_lt_sq₀ hnn1 hnn2).mp h1
  have hle : Real.exp 0.5 ≤ 2 := hexp_half_lt.le
  have h := Real.log_le_log (Real.exp_pos _) hle
  rwa [Real.log_exp] at h

/-- Upper bound `li Z ≤ 3 * Z / log Z` from a sqrt split. -/
theorem li_upper_three (Z : ℝ)
    (hZ2 : 2 ≤ Z)
    (hS2 : 2 ≤ Real.sqrt Z)
    (hSZ : Real.sqrt Z ≤ Z)
    (hlog2 : 2 ≤ Real.log Z)
    (hsq : (Real.log Z) ^ 2 ≤ Real.sqrt Z) :
    li Z ≤ 3 * Z / Real.log Z := by
  have hZpos : 0 < Z := by linarith
  have hSpos : 0 < Real.sqrt Z := by linarith [Real.sqrt_nonneg Z]
  have hlogpos : 0 < Real.log Z := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf := half_le_log_two
  have hSlogpos : 0 < Real.log (Real.sqrt Z) := by
    rw [Real.log_sqrt hZpos.le]
    linarith
  set S := Real.sqrt Z with hS
  have h2S : (2 : ℝ) ≤ S := hS2
  have hSZ' : S ≤ Z := hSZ
  have h2Z : (2 : ℝ) ≤ Z := hZ2
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc (2 : ℝ) Z) := by
    apply (Real.continuousOn_log.mono (by
      intro t ht
      exact ne_of_gt (show 0 < t by linarith [ht.1]))).inv₀
    intro t ht
    exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  have hInt2S : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume 2 S :=
    (hcont.mono (Set.Icc_subset_Icc le_rfl hSZ')).intervalIntegrable_of_Icc h2S
  have hIntSZ : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume S Z :=
    (hcont.mono (Set.Icc_subset_Icc h2S le_rfl)).intervalIntegrable_of_Icc hSZ'
  have hsplit : (∫ t : ℝ in (2 : ℝ)..Z, (Real.log t)⁻¹) =
      (∫ t : ℝ in (2 : ℝ)..S, (Real.log t)⁻¹) +
        (∫ t : ℝ in S..Z, (Real.log t)⁻¹) := by
    exact (intervalIntegral.integral_add_adjacent_intervals hInt2S hIntSZ).symm
  have hli : li Z = ∫ t : ℝ in (2 : ℝ)..Z, (Real.log t)⁻¹ := rfl
  -- First block: `1/log t ≤ 1/log 2`.
  have hfirst : (∫ t : ℝ in (2 : ℝ)..S, (Real.log t)⁻¹) ≤ S / Real.log 2 := by
    have hf : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume 2 S := hInt2S
    have hg : IntervalIntegrable (fun _ : ℝ => (Real.log 2)⁻¹) volume 2 S :=
      continuousOn_const.intervalIntegrable_of_Icc h2S
    have hmono : (∫ t : ℝ in (2 : ℝ)..S, (Real.log t)⁻¹) ≤
        ∫ t : ℝ in (2 : ℝ)..S, (Real.log 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on h2S hf hg
      intro t ht
      have ht2 : 2 ≤ t := ht.1
      have hlogt : Real.log 2 ≤ Real.log t :=
        Real.log_le_log (by norm_num) ht2
      simpa [one_div] using one_div_le_one_div_of_le hlog2pos hlogt
    calc
      (∫ t : ℝ in (2 : ℝ)..S, (Real.log t)⁻¹) ≤
          ∫ t : ℝ in (2 : ℝ)..S, (Real.log 2)⁻¹ := hmono
      _ = (S - 2) / Real.log 2 := by
        simp [smul_eq_mul, div_eq_mul_inv]
      _ ≤ S / Real.log 2 := by
        apply (div_le_div_iff_of_pos_right hlog2pos).mpr
        linarith
  -- Second block: `1/log t ≤ 1/log S`.
  have hsecond : (∫ t : ℝ in S..Z, (Real.log t)⁻¹) ≤ (Z - S) / Real.log S := by
    have hf : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume S Z := hIntSZ
    have hg : IntervalIntegrable (fun _ : ℝ => (Real.log S)⁻¹) volume S Z :=
      continuousOn_const.intervalIntegrable_of_Icc hSZ'
    have hmono : (∫ t : ℝ in S..Z, (Real.log t)⁻¹) ≤
        ∫ t : ℝ in S..Z, (Real.log S)⁻¹ := by
      apply intervalIntegral.integral_mono_on hSZ' hf hg
      intro t ht
      have hlogt : Real.log S ≤ Real.log t :=
        Real.log_le_log hSpos ht.1
      simpa [one_div] using one_div_le_one_div_of_le hSlogpos hlogt
    calc
      (∫ t : ℝ in S..Z, (Real.log t)⁻¹) ≤
          ∫ t : ℝ in S..Z, (Real.log S)⁻¹ := hmono
      _ = (Z - S) / Real.log S := by
        simp [smul_eq_mul, div_eq_mul_inv]
  have hlogS : Real.log S = Real.log Z / 2 := Real.log_sqrt hZpos.le
  have hsecond' : (∫ t : ℝ in S..Z, (Real.log t)⁻¹) ≤ 2 * Z / Real.log Z := by
    have h1 : (Z - S) / Real.log S = 2 * (Z - S) / Real.log Z := by
      rw [hlogS]
      field_simp
    have h2 : 2 * (Z - S) / Real.log Z ≤ 2 * Z / Real.log Z := by
      apply div_le_div_of_nonneg_right _ hlogpos.le
      linarith
    exact hsecond.trans (by rw [h1]; exact h2)
  have hfirst' : (∫ t : ℝ in (2 : ℝ)..S, (Real.log t)⁻¹) ≤ Z / Real.log Z := by
    -- `S / log 2 ≤ 2 * S ≤ Z / log Z`.
    have hSlog2 : S / Real.log 2 ≤ 2 * S := by
      have h1 : (1 : ℝ) / Real.log 2 ≤ 2 := by
        calc (1 : ℝ) / Real.log 2 ≤ (1 : ℝ) / 0.5 :=
              one_div_le_one_div_of_le (by norm_num) hhalf
          _ = 2 := by norm_num
      have hinv : (Real.log 2)⁻¹ ≤ 2 := by
        rw [inv_eq_one_div]
        exact h1
      calc
        S / Real.log 2 = S * (Real.log 2)⁻¹ := by ring
        _ ≤ S * 2 := mul_le_mul_of_nonneg_left hinv hSpos.le
        _ = 2 * S := by ring
    have h2S_le : 2 * S ≤ Z / Real.log Z := by
      -- `2 * log Z ≤ S` from `(log Z)^2 ≤ S` and `2 ≤ log Z`.
      have h2log : 2 * Real.log Z ≤ S := by
        have hsq' : Real.log Z * Real.log Z ≤ S := by
          simpa [pow_two] using hsq
        have hle : 2 * Real.log Z ≤ Real.log Z * Real.log Z := by
          have := mul_le_mul_of_nonneg_right hlog2 hlogpos.le
          simpa [mul_comm] using this
        linarith
      have hSpos' : 0 < S := hSpos
      have hZZ : S * S = Z := Real.mul_self_sqrt hZpos.le
      rw [le_div_iff₀ hlogpos]
      nlinarith [h2log, hSpos', hZZ]
    exact hfirst.trans (hSlog2.trans h2S_le)
  calc
    li Z = (∫ t : ℝ in (2 : ℝ)..S, (Real.log t)⁻¹) +
        (∫ t : ℝ in S..Z, (Real.log t)⁻¹) := by rw [hli, hsplit]
    _ ≤ Z / Real.log Z + 2 * Z / Real.log Z := add_le_add hfirst' hsecond'
    _ = 3 * Z / Real.log Z := by ring

/-- `sqrt y ≤ a * y` once `y ≥ (1/a)^2`. -/
theorem sqrt_le_mul_of_ge (a y : ℝ) (ha : 0 < a)
    (hy : (1 / a) ^ 2 ≤ y) (hy0 : 0 < y) :
    Real.sqrt y ≤ a * y := by
  have ha2 : (0 : ℝ) < 1 / a := by positivity
  have h_sqrt_ge : 1 / a ≤ Real.sqrt y := by
    have h_eq : (1 / a) = Real.sqrt ((1 / a) ^ 2) :=
      (Real.sqrt_sq ha2.le).symm
    rw [h_eq]
    exact Real.sqrt_le_sqrt hy
  have h1_le : (1 : ℝ) ≤ a * Real.sqrt y := by
    have hmul := mul_le_mul_of_nonneg_left h_sqrt_ge ha.le
    have hcancel : a * (1 / a) = 1 := mul_one_div_cancel ha.ne'
    linarith [hmul, hcancel]
  have h_eq_y : y = Real.sqrt y * Real.sqrt y :=
    (Real.mul_self_sqrt hy0.le).symm
  calc Real.sqrt y = 1 * Real.sqrt y := by ring
    _ ≤ (a * Real.sqrt y) * Real.sqrt y :=
      mul_le_mul_of_nonneg_right h1_le (Real.sqrt_nonneg _)
    _ = a * y := by
      conv_rhs => rw [h_eq_y]
      ring

/-- `a * y ≤ y^2` once `a ≤ y` and `0 ≤ y`. -/
theorem mul_le_sq_of_ge (a y : ℝ) (hay : a ≤ y) (hy0 : 0 ≤ y) :
    a * y ≤ y ^ 2 := by
  calc a * y ≤ y * y := mul_le_mul_of_nonneg_right hay hy0
    _ = y ^ 2 := by ring

/-- Log sandwich from sqrt/square bounds. -/
theorem log_sandwich_of_bounds (a y : ℝ) (haypos : 0 < a * y) (hy1 : 1 ≤ y)
    (hsqrt : Real.sqrt y ≤ a * y) (hsq : a * y ≤ y ^ 2) :
    Real.log y / 2 ≤ Real.log (a * y) ∧ Real.log (a * y) ≤ 2 * Real.log y := by
  have hypos : 0 < y := by linarith
  have hlog_sqrt_le : Real.log (Real.sqrt y) ≤ Real.log (a * y) :=
    Real.log_le_log (Real.sqrt_pos.mpr hypos) hsqrt
  have hlog_sqrt_eq : Real.log (Real.sqrt y) = Real.log y / 2 :=
    Real.log_sqrt hypos.le
  have hlower : Real.log y / 2 ≤ Real.log (a * y) :=
    hlog_sqrt_eq ▸ hlog_sqrt_le
  have hupper : Real.log (a * y) ≤ 2 * Real.log y := by
    have hle : Real.log (a * y) ≤ Real.log (y ^ 2) :=
      Real.log_le_log haypos hsq
    rw [Real.log_pow] at hle
    simpa using hle
  exact ⟨hlower, hupper⟩

/-- First error `K*Z/logZ^3 ≤ (Z-Y)/(4*logZ)` from `logZ^2 ≥ 4*K*b/d`. -/
theorem error_Z_le (K b d y logZ : ℝ) (_hK : 0 < K) (_hb : 0 < b) (hd : 0 < d)
    (hy : 0 < y) (hlog : 0 < logZ) (hlog2 : 4 * K * b / d ≤ logZ ^ 2) :
    K * (b * y) / (logZ ^ 3) ≤ (d * y) / (4 * logZ) := by
  have hlog3 : (0 : ℝ) < logZ ^ 3 := pow_pos hlog 3
  have h4log : (0 : ℝ) < 4 * logZ := by positivity
  rw [div_le_div_iff₀ hlog3 h4log]
  have hpow : logZ ^ 3 = logZ ^ 2 * logZ := by ring
  rw [hpow]
  have hdpos : (0 : ℝ) < d := hd
  have hylog : (0 : ℝ) ≤ y * logZ := (mul_nonneg hy.le hlog.le)
  have hmain : 4 * K * b ≤ d * logZ ^ 2 := by
    rw [div_le_iff₀ hd] at hlog2
    linarith [hlog2]
  nlinarith [hmain, hylog, hlog.le, hy.le, mul_nonneg hy.le hlog.le,
    mul_le_mul_of_nonneg_left hmain hylog]

theorem error_Y_le (K a d y logY logZ : ℝ) (hK : 0 < K) (ha : 0 < a)
    (hd : 0 < d) (hy : 0 < y) (hlogY : 0 < logY) (hlogZ : 0 < logZ)
    (hle : logZ ≤ 4 * logY) (hlog2 : 16 * K * a / d ≤ logY ^ 2) :
    K * (a * y) / (logY ^ 3) ≤ (d * y) / (4 * logZ) := by
  have hlog3Y : (0 : ℝ) < logY ^ 3 := pow_pos hlogY _
  have h4logZ : (0 : ℝ) < 4 * logZ := by positivity
  rw [div_le_div_iff₀ hlog3Y h4logZ]
  have hpowY : logY ^ 3 = logY ^ 2 * logY := by ring
  rw [hpowY]
  have hmain : 16 * K * a ≤ d * logY ^ 2 := by
    rw [div_le_iff₀ hd] at hlog2
    linarith [hlog2]
  -- `4*K*a*logZ ≤ d*logY^2*logY /... `; use `logZ ≤ 4*logY`.
  have hypos : (0 : ℝ) ≤ y := hy.le
  have hlogYpos : (0 : ℝ) ≤ logY := hlogY.le
  nlinarith [hmain, hle, hypos, hlogYpos, hlogZ.le,
    mul_nonneg hypos hlogYpos, sq_nonneg logY, sq_nonneg logZ,
    mul_le_mul_of_nonneg_left hle (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * K * a) hypos)]

end Erdos821.P7Win

namespace Erdos821.P7Core
open Erdos821.Blueprint

theorem PrimeWindowHarmonicTask_proof : PrimeWindowHarmonicTask := by
  intro hC a b ha hab
  have hb : 0 < b := lt_trans ha hab
  have hd_pos : 0 < b - a := sub_pos.mpr hab
  obtain ⟨K, hK, hP⟩ := Erdos821.P7Win.prime_count_li_accuracy hC
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hP
  obtain ⟨T₁, hT₁⟩ :=
    Filter.eventually_atTop.mp
      (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow (2 : ℝ)
        (show (0 : ℝ) < 1 / 2 by norm_num))
  -- Constants.
  set d : ℝ := b - a with hd
  have hd0 : 0 < d := hd_pos
  set cmin : ℝ := d / (4 * b) with hcmin
  set cmax : ℝ := 8 * b / a with hcmax
  have hcmin_pos : 0 < cmin := by
    dsimp [cmin]
    positivity
  have hcmax_pos : 0 < cmax := by
    dsimp [cmax]
    positivity
  set B1 : ℝ := 4 * K * b / d with hB1
  set B2 : ℝ := 16 * K * a / d with hB2
  set B3 : ℝ := K with hB3
  have hB1_pos : 0 < B1 := by dsimp [B1]; positivity
  have hB2_pos : 0 < B2 := by dsimp [B2]; positivity
  have hB3_pos : 0 < B3 := by dsimp [B3]; exact hK
  set L : ℝ := 2 * Real.sqrt B1 + 2 * Real.sqrt B2 + 2 * Real.sqrt B3 + 4 with hL
  have hL4 : 4 ≤ L := by
    dsimp [L]
    have h1 : (0 : ℝ) ≤ 2 * Real.sqrt B1 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * Real.sqrt B2 := by positivity
    have h3 : (0 : ℝ) ≤ 2 * Real.sqrt B3 := by positivity
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hLB1 : 2 * Real.sqrt B1 ≤ L := by
    dsimp [L]
    have h2 : (0 : ℝ) ≤ 2 * Real.sqrt B2 := by positivity
    have h3 : (0 : ℝ) ≤ 2 * Real.sqrt B3 := by positivity
    linarith
  have hLB2 : 2 * Real.sqrt B2 ≤ L := by
    dsimp [L]
    have h1 : (0 : ℝ) ≤ 2 * Real.sqrt B1 := by positivity
    have h3 : (0 : ℝ) ≤ 2 * Real.sqrt B3 := by positivity
    linarith
  have hLB3 : 2 * Real.sqrt B3 ≤ L := by
    dsimp [L]
    have h1 : (0 : ℝ) ≤ 2 * Real.sqrt B1 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * Real.sqrt B2 := by positivity
    linarith
  refine ⟨cmin, cmax, hcmin_pos, hcmax_pos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (Y₀ / a),
    Filter.eventually_ge_atTop (Y₀ / b),
    Filter.eventually_ge_atTop (2 / a),
    Filter.eventually_ge_atTop (2 / b),
    Filter.eventually_ge_atTop (T₁ / a),
    Filter.eventually_ge_atTop (T₁ / b),
    Filter.eventually_ge_atTop ((1 / a) ^ 2),
    Filter.eventually_ge_atTop ((1 / b) ^ 2),
    Filter.eventually_ge_atTop a,
    Filter.eventually_ge_atTop b,
    Filter.eventually_ge_atTop (Real.exp L)] with y hyY0a hyY0b hy2a hy2b hyT1a hyT1b
      hySqA hySqB hya hyb hyExp
  -- Basic positivity.
  have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos L) hyExp
  have hY : 0 < a * y := mul_pos ha hypos
  have hZ : 0 < b * y := mul_pos hb hypos
  have h1y : 1 ≤ y := le_trans (Real.one_le_exp hL0) hyExp
  set Y : ℝ := a * y with hYdef
  set Z : ℝ := b * y with hZdef
  have hYZ : Y ≤ Z := by
    dsimp [Y, Z]
    exact mul_le_mul_of_nonneg_right hab.le hypos.le
  have hY0Y : Y₀ ≤ Y := by
    have h : Y₀ / a ≤ y := hyY0a
    have h' : Y₀ ≤ y * a := (div_le_iff₀ ha).mp h
    simpa [mul_comm, hYdef] using h'
  have hY0Z : Y₀ ≤ Z := by
    have h : Y₀ / b ≤ y := hyY0b
    have h' : Y₀ ≤ y * b := (div_le_iff₀ hb).mp h
    simpa [mul_comm, hZdef] using h'
  have h2Y : 2 ≤ Y := by
    have h : 2 / a ≤ y := hy2a
    have h' : 2 ≤ y * a := (div_le_iff₀ ha).mp h
    simpa [mul_comm, hYdef] using h'
  have h2Z : 2 ≤ Z := by
    have h : 2 / b ≤ y := hy2b
    have h' : 2 ≤ y * b := (div_le_iff₀ hb).mp h
    simpa [mul_comm, hZdef] using h'
  have hT1Y : T₁ ≤ Y := by
    have h : T₁ / a ≤ y := hyT1a
    have h' : T₁ ≤ y * a := (div_le_iff₀ ha).mp h
    simpa [mul_comm, hYdef] using h'
  have hT1Z : T₁ ≤ Z := by
    have h : T₁ / b ≤ y := hyT1b
    have h' : T₁ ≤ y * b := (div_le_iff₀ hb).mp h
    simpa [mul_comm, hZdef] using h'
  have hLogY : L ≤ Real.log y := (Real.le_log_iff_exp_le hypos).mpr hyExp
  have hLpos : 0 < L := by linarith only [hL4]
  have hlogy_pos : 0 < Real.log y := lt_of_lt_of_le hLpos hLogY
  have hlogy1 : 1 ≤ Real.log y :=
    le_trans (by linarith only [hL4] : (1 : ℝ) ≤ L) hLogY
  -- Sqrt/square bounds and log sandwich.
  have hsqrtA : Real.sqrt y ≤ a * y :=
    Erdos821.P7Win.sqrt_le_mul_of_ge a y ha hySqA hypos
  have hsqrtB : Real.sqrt y ≤ b * y :=
    Erdos821.P7Win.sqrt_le_mul_of_ge b y hb hySqB hypos
  have hsqA : a * y ≤ y ^ 2 :=
    Erdos821.P7Win.mul_le_sq_of_ge a y hya hypos.le
  have hsqB : b * y ≤ y ^ 2 :=
    Erdos821.P7Win.mul_le_sq_of_ge b y hyb hypos.le
  obtain ⟨hlogY_lo, hlogY_hi⟩ :=
    Erdos821.P7Win.log_sandwich_of_bounds a y hY h1y hsqrtA hsqA
  obtain ⟨hlogZ_lo, hlogZ_hi⟩ :=
    Erdos821.P7Win.log_sandwich_of_bounds b y hZ h1y hsqrtB hsqB
  have hlogY_pos : 0 < Real.log Y :=
    lt_of_lt_of_le (div_pos hlogy_pos (by norm_num)) hlogY_lo
  have hlogZ_pos : 0 < Real.log Z :=
    lt_of_lt_of_le (div_pos hlogy_pos (by norm_num)) hlogZ_lo
  have hlogY2 : 2 ≤ Real.log Y :=
    le_trans (by linarith only [hL4] : (2 : ℝ) ≤ L / 2)
      (le_trans (by linarith only [hLogY] : L / 2 ≤ Real.log y / 2) hlogY_lo)
  have hlogZ2 : 2 ≤ Real.log Z :=
    le_trans (by linarith only [hL4] : (2 : ℝ) ≤ L / 2)
      (le_trans (by linarith only [hLogY] : L / 2 ≤ Real.log y / 2) hlogZ_lo)
  have hlogZ_le_4Y : Real.log Z ≤ 4 * Real.log Y := by
    have h1 : Real.log y ≤ 2 * Real.log Y := by linarith only [hlogY_lo]
    linarith only [hlogZ_hi, h1]
  -- `log^2 ≥ B` from `log y ≥ L`.
  have hlogY_ge_sqrtB2 : Real.sqrt B2 ≤ Real.log Y := by
    have h1 : Real.sqrt B2 ≤ L / 2 := by linarith only [hLB2]
    have h2 : L / 2 ≤ Real.log Y := by
      have h3 : L / 2 ≤ Real.log y / 2 := by linarith only [hLogY]
      linarith only [h3, hlogY_lo]
    linarith only [h1, h2]
  have hlogZ_ge_sqrtB1 : Real.sqrt B1 ≤ Real.log Z := by
    have h1 : Real.sqrt B1 ≤ L / 2 := by linarith only [hLB1]
    have h2 : L / 2 ≤ Real.log Z := by
      have h3 : L / 2 ≤ Real.log y / 2 := by linarith only [hLogY]
      linarith only [h3, hlogZ_lo]
    linarith only [h1, h2]
  have hlogZ_ge_sqrtB3 : Real.sqrt B3 ≤ Real.log Z := by
    have h1 : Real.sqrt B3 ≤ L / 2 := by linarith only [hLB3]
    have h2 : L / 2 ≤ Real.log Z := by
      have h3 : L / 2 ≤ Real.log y / 2 := by linarith only [hLogY]
      linarith only [h3, hlogZ_lo]
    linarith only [h1, h2]
  have hlogY2_B2 : B2 ≤ Real.log Y ^ 2 := by
    have hle : Real.sqrt B2 ^ 2 ≤ Real.log Y ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hlogY_ge_sqrtB2 2
    rwa [Real.sq_sqrt hB2_pos.le] at hle
  have hlogZ2_B1 : B1 ≤ Real.log Z ^ 2 := by
    have hle : Real.sqrt B1 ^ 2 ≤ Real.log Z ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hlogZ_ge_sqrtB1 2
    rwa [Real.sq_sqrt hB1_pos.le] at hle
  have hlogZ2_B3 : B3 ≤ Real.log Z ^ 2 := by
    have hle : Real.sqrt B3 ^ 2 ≤ Real.log Z ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hlogZ_ge_sqrtB3 2
    rwa [Real.sq_sqrt hB3_pos.le] at hle
  have hB1_eq : 4 * K * b / d ≤ Real.log Z ^ 2 := by simpa [hB1] using hlogZ2_B1
  have hB2_eq : 16 * K * a / d ≤ Real.log Y ^ 2 := by simpa [hB2] using hlogY2_B2
  have hB3_eq : K ≤ Real.log Z ^ 2 := by simpa [hB3] using hlogZ2_B3
  -- OAI square-root bound for `li` upper.
  have hOAI_Z : (Real.log Z) ^ 2 ≤ Real.sqrt Z := by
    have h := hT₁ Z hT1Z
    have hconv1 : (Real.log Z) ^ (2 : ℝ) = (Real.log Z) ^ 2 := by
      have : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    have hconv2 : Z ^ ((1 : ℝ) / 2) = Real.sqrt Z := (Real.sqrt_eq_rpow Z).symm
    have h' : (Real.log Z) ^ (2 : ℝ) ≤ Z ^ ((1 : ℝ) / 2) := by
      simpa using h
    rwa [hconv1, hconv2] at h'
  have hOAI_Y : (Real.log Y) ^ 2 ≤ Real.sqrt Y := by
    have h := hT₁ Y hT1Y
    have hconv1 : (Real.log Y) ^ (2 : ℝ) = (Real.log Y) ^ 2 := by
      have : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    have hconv2 : Y ^ ((1 : ℝ) / 2) = Real.sqrt Y := (Real.sqrt_eq_rpow Y).symm
    have h' : (Real.log Y) ^ (2 : ℝ) ≤ Y ^ ((1 : ℝ) / 2) := by
      simpa using h
    rwa [hconv1, hconv2] at h'
  have hsqrtZ2 : 2 ≤ Real.sqrt Z := by
    have h4 : (4 : ℝ) ≤ Real.log Z ^ 2 := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ Real.log Z ^ 2 :=
          pow_le_pow_left₀ (by norm_num) hlogZ2 2
    linarith only [hOAI_Z, h4]
  have hsqrtZZ : Real.sqrt Z ≤ Z := by
    have h1Z : (1 : ℝ) ≤ Z := by linarith only [h2Z]
    have hZZ : Z ≤ Z ^ 2 := by
      calc Z = Z * 1 := by ring
        _ ≤ Z * Z := mul_le_mul_of_nonneg_left h1Z (by linarith only [h2Z])
        _ = Z ^ 2 := by ring
    have h0Z : (0 : ℝ) ≤ Z := by linarith only [h2Z]
    have := (Real.sqrt_le_left h0Z).mpr hZZ
    simpa using this
  have hliZ : Erdos821.Blueprint.li Z ≤ 3 * Z / Real.log Z :=
    Erdos821.P7Win.li_upper_three Z h2Z hsqrtZ2 hsqrtZZ hlogZ2 hOAI_Z
  -- PNT errors.
  have herrY := hY₀ Y hY0Y
  have herrZ := hY₀ Z hY0Z
  have heY_eq : K * Y * Real.log Y ^ (-3 : ℝ) = K * Y / (Real.log Y ^ 3) := by
    rw [Erdos821.P7Win.rpow_neg_three_eq Y hlogY_pos]
    ring
  have heZ_eq : K * Z * Real.log Z ^ (-3 : ℝ) = K * Z / (Real.log Z ^ 3) := by
    rw [Erdos821.P7Win.rpow_neg_three_eq Z hlogZ_pos]
    ring
  rw [heY_eq] at herrY
  rw [heZ_eq] at herrZ
  have hZY : Y ≤ Z := hYZ
  have hli_lower := Erdos821.P7Win.li_interval_lower Y Z h2Y hZY
  have hcard_lower := Erdos821.P7Win.interval_card_lower Y Z
    (K * Y / (Real.log Y ^ 3)) (K * Z / (Real.log Z ^ 3)) hZY herrY herrZ
  -- Main term and quarter errors.
  have hZY_lt : Y < Z := by
    dsimp [Y, Z]
    exact mul_lt_mul_of_pos_right hab hypos
  have hMpos : 0 < (Z - Y) / Real.log Z :=
    div_pos (sub_pos.mpr hZY_lt) hlogZ_pos
  have heZ_le : K * Z / (Real.log Z ^ 3) ≤ (Z - Y) / (4 * Real.log Z) := by
    have hZZ' : Z = b * y := rfl
    have hZY' : Z - Y = d * y := by dsimp [Y, Z, d]; ring
    rw [hZZ', hZY']
    exact Erdos821.P7Win.error_Z_le K b d y (Real.log Z) hK hb hd0 hypos
      hlogZ_pos hB1_eq
  have heY_le : K * Y / (Real.log Y ^ 3) ≤ (Z - Y) / (4 * Real.log Z) := by
    have hYY' : Y = a * y := rfl
    have hZY' : Z - Y = d * y := by dsimp [Y, Z, d]; ring
    rw [hYY', hZY']
    exact Erdos821.P7Win.error_Y_le K a d y (Real.log Y) (Real.log Z) hK ha hd0
      hypos hlogY_pos hlogZ_pos hlogZ_le_4Y hB2_eq
  have hcard_half : (Z - Y) / (2 * Real.log Z) ≤
      (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) := by
    have h1 : (Z - Y) / Real.log Z - K * Z / (Real.log Z ^ 3) -
        K * Y / (Real.log Y ^ 3) ≤
        (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) := by
      linarith only [hcard_lower, hli_lower]
    have h2 : (Z - Y) / (2 * Real.log Z) =
        (Z - Y) / Real.log Z - (Z - Y) / (4 * Real.log Z) -
          (Z - Y) / (4 * Real.log Z) := by
      ring
    linarith only [h1, heZ_le, heY_le, h2]
  -- Lower reciprocal mass.
  have hsum_ge := Erdos821.P7Win.window_sum_ge_card_div Y Z hZ
  have hcard_div : (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) / Z ≤
      ∑ p ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := hsum_ge
  have hlower_main : d / (2 * b * Real.log Z) ≤
      ∑ p ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
    have h1 : (Z - Y) / (2 * Real.log Z) / Z = d / (2 * b * Real.log Z) := by
      dsimp [Y, Z, d]
      field_simp [hypos.ne', hb.ne', hlogZ_pos.ne']
    have h2 : (Z - Y) / (2 * Real.log Z) / Z ≤
        ∑ p ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
      calc (Z - Y) / (2 * Real.log Z) / Z ≤
          (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) / Z :=
            div_le_div_of_nonneg_right hcard_half hZ.le
        _ ≤ _ := hcard_div
    rwa [h1] at h2
  have hlogZ_le_2y : Real.log Z ≤ 2 * Real.log y := hlogZ_hi
  have hlower : cmin / Real.log y ≤
      ∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
    have h1 : cmin / Real.log y = d / (4 * b * Real.log y) := by dsimp [cmin]; ring
    have h2 : d / (4 * b * Real.log y) ≤ d / (2 * b * Real.log Z) := by
      have hpos : (0 : ℝ) < d / (2 * b) := by positivity
      have hinv : (1 : ℝ) / (2 * Real.log y) ≤ (1 : ℝ) / Real.log Z :=
        one_div_le_one_div_of_le hlogZ_pos hlogZ_hi
      calc d / (4 * b * Real.log y) = (d / (2 * b)) * ((1 : ℝ) / (2 * Real.log y)) := by
            ring
        _ ≤ (d / (2 * b)) * ((1 : ℝ) / Real.log Z) :=
          mul_le_mul_of_nonneg_left hinv hpos.le
        _ = d / (2 * b * Real.log Z) := by ring
    have h3 : d / (2 * b * Real.log Z) ≤
        ∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
      simpa [Y, Z] using hlower_main
    linarith only [h1, h2, h3]
  -- Upper reciprocal mass via total count.
  have hY1 : 1 ≤ ⌈Y⌉₊ := by
    have h1Y : (1 : ℝ) ≤ Y := by linarith only [h2Y]
    have hle : (1 : ℝ) ≤ (⌈Y⌉₊ : ℝ) := le_trans h1Y (Nat.le_ceil Y)
    have hcast : ((1 : ℕ) : ℝ) ≤ (⌈Y⌉₊ : ℝ) := by simpa using hle
    exact_mod_cast hcast
  have hcard_up := Erdos821.P7Win.icc_card_le_primesUpTo Y Z hY1
  have hsum_le := Erdos821.P7Win.window_sum_le_card_div Y Z (by dsimp [Y]; exact hY)
  have hpiZ_le : ((primesUpTo Z).card : ℝ) ≤ 4 * Z / Real.log Z := by
    have hle : ((primesUpTo Z).card : ℝ) - li Z ≤ K * Z / (Real.log Z ^ 3) :=
      (abs_le.mp herrZ).2
    have heZ_le_up : K * Z / (Real.log Z ^ 3) ≤ Z / Real.log Z := by
      have hlog2 : K ≤ Real.log Z ^ 2 := by simpa [hB3] using hB3_eq
      have hlog3 : (0 : ℝ) < Real.log Z ^ 3 := pow_pos hlogZ_pos 3
      have h1log : (0 : ℝ) < Real.log Z := hlogZ_pos
      have h1 : K / (Real.log Z ^ 3) ≤ 1 / Real.log Z := by
        rw [div_le_div_iff₀ hlog3 h1log]
        have hpow : Real.log Z ^ 3 = Real.log Z ^ 2 * Real.log Z := by ring
        rw [hpow]
        have hle' : K * Real.log Z ≤ Real.log Z ^ 2 * Real.log Z :=
          mul_le_mul_of_nonneg_right hlog2 h1log.le
        simpa using hle'
      calc K * Z / (Real.log Z ^ 3) = Z * (K / (Real.log Z ^ 3)) := by ring
        _ ≤ Z * (1 / Real.log Z) :=
          mul_le_mul_of_nonneg_left h1 hZ.le
        _ = Z / Real.log Z := by ring
    have hle2 : ((primesUpTo Z).card : ℝ) - li Z ≤ Z / Real.log Z :=
      le_trans hle heZ_le_up
    calc ((primesUpTo Z).card : ℝ)
        = li Z + (((primesUpTo Z).card : ℝ) - li Z) := by ring
      _ ≤ 3 * Z / Real.log Z + Z / Real.log Z := add_le_add hliZ hle2
      _ = 4 * Z / Real.log Z := by ring
  have hupper_main : ∑ p ∈ (Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ≤
      4 * b / (a * Real.log Z) := by
    have h1 : (((Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) / Y ≤
        4 * b / (a * Real.log Z) := by
      have hcard : (((Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) ≤
          4 * Z / Real.log Z := le_trans (by exact_mod_cast hcard_up) hpiZ_le
      have hYeq : Y = a * y := rfl
      have hZeq : Z = b * y := rfl
      have hYpos : 0 < Y := by rw [hYeq]; exact hY
      have hle : (((Finset.Icc ⌈Y⌉₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) / Y ≤
          (4 * Z / Real.log Z) / Y :=
        (div_le_div_iff_of_pos_right hYpos).mpr hcard
      have heq : (4 * Z / Real.log Z) / Y = 4 * b / (a * Real.log Z) := by
        rw [hYeq, hZeq]
        field_simp [hypos.ne', ha.ne', hb.ne', hlogZ_pos.ne']
      rwa [heq] at hle
    exact le_trans hsum_le h1
  have hupper : ∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ≤
      cmax / Real.log y := by
    have h1 : (4 * b / (a * Real.log Z)) ≤ cmax / Real.log y := by
      dsimp [cmax]
      have hpos : (0 : ℝ) < 4 * b / a := by positivity
      have hinv : (1 : ℝ) / Real.log Z ≤ 2 / Real.log y := by
        have hle : Real.log y / 2 ≤ Real.log Z := hlogZ_lo
        have hpos2 : (0 : ℝ) < Real.log y / 2 := div_pos hlogy_pos (by norm_num)
        have h1 : (1 : ℝ) / Real.log Z ≤ (1 : ℝ) / (Real.log y / 2) :=
          one_div_le_one_div_of_le hpos2 hle
        have heq : (1 : ℝ) / (Real.log y / 2) = 2 / Real.log y := by ring
        rwa [heq] at h1
      calc 4 * b / (a * Real.log Z) = (4 * b / a) * ((1 : ℝ) / Real.log Z) := by
            ring
        _ ≤ (4 * b / a) * (2 / Real.log y) :=
          mul_le_mul_of_nonneg_left hinv hpos.le
        _ = 8 * b / a / Real.log y := by ring
    have h2 : ∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ≤
        4 * b / (a * Real.log Z) := by simpa [Y, Z] using hupper_main
    linarith only [h1, h2]
  exact ⟨hlower, hupper⟩

example : PrimeWindowHarmonicTask = PrimeWindowHarmonicTask := rfl

end Erdos821.P7Core

