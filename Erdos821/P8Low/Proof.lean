import Erdos821.Blueprint.Proxy
import Erdos821.Blueprint.Classical
import Erdos821.P8Int.Integral
import OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem

noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Low
open Blueprint Blueprint.Analytic

/-- Lower-density bound for ordinary dyadic rough counts. -/
def RoughDyadicDensityLowerTask : Prop :=
  ClassicalInputs → ∀ b : ℝ, 0 < b → b < 1 →
    ∀ eps : ℝ, 0 < eps → ∀ᶠ x : ℝ in atTop,
      roughDensity b 1 - eps ≤ L x / x *
        (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b))).card : ℝ)
theorem prime_count_li_accuracy (hC : ClassicalInputs) (A C : ℝ)
    (hA : 0 < A) (hCpos : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ y : ℝ in atTop,
      |((primesUpTo y).card : ℝ) - li y| ≤ K * y * Real.log y ^ (-A) := by
  obtain ⟨K, hK, hP⟩ := hC.progressions A C hA hCpos
  refine ⟨K, hK, ?_⟩
  filter_upwards [hP, Filter.eventually_gt_atTop (Real.exp 1)] with y hy hlarge
  have hc : Nat.Coprime 0 1 := by norm_num
  have hlog : 1 ≤ Real.log y :=
    (Real.le_log_iff_exp_le (lt_trans (Real.exp_pos 1) hlarge)).2 hlarge.le
  have hpow : 1 ≤ Real.log y ^ C := Real.one_le_rpow hlog hCpos.le
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

theorem prime_interval_card (Y Z : ℝ) (hYZ : ⌊Y⌋₊ ≤ ⌊Z⌋₊) :
    ((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card =
      (primesUpTo Z).card - (primesUpTo Y).card := by
  have h := prime_interval_card_add Y Z hYZ
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

theorem prime_interval_count_le (hC : ClassicalInputs) (A C : ℝ)
    (hA : 0 < A) (hCpos : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Y : ℝ in atTop, ∀ Z : ℝ, Y ≤ Z →
      (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) ≤
        li Z - li Y + K * Z * Real.log Z ^ (-A) + K * Y * Real.log Y ^ (-A) := by
  obtain ⟨K, hK, hP⟩ := prime_count_li_accuracy hC A C hA hCpos
  have ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hP
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop Y₀] with Y hY
  intro Z hYZ
  have hYerr := hY₀ Y hY
  have hZerr := hY₀ Z (hY.trans hYZ)
  have hcard := prime_interval_card_add Y Z (Nat.floor_mono hYZ)
  have hZupper : ((primesUpTo Z).card : ℝ) ≤ li Z + K * Z * Real.log Z ^ (-A) := by
    have hh := (abs_le.mp hZerr).2
    linarith
  have hYlower : li Y - K * Y * Real.log Y ^ (-A) ≤ (primesUpTo Y).card := by
    have hh := (abs_le.mp hYerr).1
    linarith
  have hcardReal :
      (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) +
        (primesUpTo Y).card = (primesUpTo Z).card := by
    exact_mod_cast hcard
  linarith

theorem prime_interval_count_ge (hC : ClassicalInputs) (A C : ℝ)
    (hA : 0 < A) (hCpos : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Y : ℝ in atTop, ∀ Z : ℝ, Y ≤ Z →
      li Z - li Y - K * Z * Real.log Z ^ (-A) - K * Y * Real.log Y ^ (-A) ≤
        (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) := by
  obtain ⟨K, hK, hP⟩ := prime_count_li_accuracy hC A C hA hCpos
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hP
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop Y₀] with Y hY
  intro Z hYZ
  have hYerr := hY₀ Y hY
  have hZerr := hY₀ Z (hY.trans hYZ)
  have hcard := prime_interval_card_add Y Z (Nat.floor_mono hYZ)
  have hZlower : li Z - K * Z * Real.log Z ^ (-A) ≤ (primesUpTo Z).card := by
    have hh := (abs_le.mp hZerr).1
    linarith
  have hYupper : (primesUpTo Y).card ≤ li Y + K * Y * Real.log Y ^ (-A) := by
    have hh := (abs_le.mp hYerr).2
    linarith
  have hcardReal :
      (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) +
        (primesUpTo Y).card = (primesUpTo Z).card := by
    exact_mod_cast hcard
  linarith

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

theorem prime_dyadic_count_lower (hC : ClassicalInputs) {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) :
    ∀ᶠ Y : ℝ in atTop,
      (1 - eps) * Y / Real.log Y ≤
        (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime).card : ℝ) := by
  obtain ⟨K, hK, hIntervals⟩ :=
    prime_interval_count_ge hC 2 1 (by norm_num) (by norm_num)
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hIntervals
  let B : ℝ := max 1 (max (12 * K / eps) (4 * Real.log 2 / eps))
  have hB : 0 < B := by dsimp [B]; positivity
  have hlogEvent : ∀ᶠ Y : ℝ in atTop, B ≤ Real.log Y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop B)
  filter_upwards [eventually_ge_atTop Y₀, hlogEvent, eventually_ge_atTop (2 : ℝ)]
      with Y hY hlog hYge2
  have hYpos : 0 < Y := by linarith
  have hlogpos : 0 < Real.log Y := by
    have hB1 : 1 ≤ B := le_max_left _ _
    exact lt_of_lt_of_le zero_lt_one (hB1.trans hlog)
  have h2Y : 2 ≤ 2 * Y := by nlinarith
  have hYZ : Y ≤ 2 * Y := by nlinarith
  have hcount := hY₀ Y hY (2 * Y) hYZ
  have hli := li_interval_lower Y (2 * Y) hYge2 hYZ
  have hli' : Y / Real.log (2 * Y) ≤ li (2 * Y) - li Y := by
    convert hli using 1 <;> ring
  have hlog2 : Real.log (2 * Y) = Real.log 2 + Real.log Y := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYpos.ne']
  have hlogUpper : Real.log (2 * Y) ≤ (1 + eps / 4) * Real.log Y := by
    rw [hlog2]
    have hmax : 4 * Real.log 2 / eps ≤ B :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have h := hmax.trans hlog
    have hmul : 4 * Real.log 2 ≤ eps * Real.log Y := by
      simpa [mul_comm] using (div_le_iff₀ heps).mp h
    nlinarith
  have hlog2pos : 0 < Real.log (2 * Y) := Real.log_pos (by linarith [h2Y])
  have hmain : Y / Real.log (2 * Y) ≥ (1 - eps / 4) * Y / Real.log Y := by
    have hden : 0 < (1 + eps / 4) * Real.log Y := by positivity
    have hfrac : (1 - eps / 4) ≤ (1 + eps / 4)⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ (by positivity)).2
      nlinarith [sq_nonneg (eps / 4)]
    have hrecip : ((1 + eps / 4) * Real.log Y)⁻¹ ≤ (Real.log (2 * Y))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hlog2pos hlogUpper
    have hbound : (Real.log (2 * Y))⁻¹ ≥
        (1 - eps / 4) * (Real.log Y)⁻¹ := by
      calc
        (Real.log (2 * Y))⁻¹ ≥ ((1 + eps / 4) * Real.log Y)⁻¹ := hrecip
        _ = (1 + eps / 4)⁻¹ * (Real.log Y)⁻¹ := by field_simp
        _ ≥ (1 - eps / 4) * (Real.log Y)⁻¹ :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
    calc
      Y / Real.log (2 * Y) = Y * (Real.log (2 * Y))⁻¹ := by ring
      _ ≥ Y * ((1 - eps / 4) * (Real.log Y)⁻¹) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (1 - eps / 4) * Y / Real.log Y := by ring
  have hlogMono : Real.log Y ≤ Real.log (2 * Y) :=
    Real.log_le_log hYpos hYZ
  have hpowMono :
      Real.log (2 * Y) ^ (-2 : ℝ) ≤ Real.log Y ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlogpos hlogMono (by norm_num)
  have herrBound :
      K * (2 * Y) * Real.log (2 * Y) ^ (-2 : ℝ) +
        K * Y * Real.log Y ^ (-2 : ℝ) ≤ eps / 4 * (Y / Real.log Y) := by
    have hsmall : 12 * K / eps ≤ Real.log Y := by
      exact (le_trans (le_max_left _ _) (le_max_right _ _)).trans hlog
    have hKpos : 0 ≤ K := hK.le
    calc
      _ ≤ 3 * K * Y * Real.log Y ^ (-2 : ℝ) := by
        have hterm := mul_le_mul_of_nonneg_left hpowMono (by positivity : 0 ≤ 2 * K * Y)
        nlinarith [hterm]
      _ ≤ eps / 4 * (Y / Real.log Y) := by
        have hmul : 12 * K ≤ eps * Real.log Y := by
          simpa [mul_comm] using (div_le_iff₀ heps).mp hsmall
        have hpow : Real.log Y ^ (-2 : ℝ) = (Real.log Y)⁻¹ * (Real.log Y)⁻¹ := by
          rw [show (-2 : ℝ) = -1 + -1 by norm_num, Real.rpow_add hlogpos]
          simp [Real.rpow_neg hlogpos.le]
        rw [hpow]
        field_simp [ne_of_gt hlogpos]
        have hmulY := mul_le_mul_of_nonneg_right hmul hYpos.le
        nlinarith [hmulY]
  have hratio : 0 < Y / Real.log Y := div_pos hYpos hlogpos
  have hmain' : (1 - eps / 4) * (Y / Real.log Y) ≤ Y / Real.log (2 * Y) := by
    calc
      (1 - eps / 4) * (Y / Real.log Y) = (1 - eps / 4) * Y / Real.log Y := by ring
      _ ≤ Y / Real.log (2 * Y) := hmain
  have htarget : (1 - eps) * Y / Real.log Y ≤
      Y / Real.log (2 * Y) -
        (K * (2 * Y) * Real.log (2 * Y) ^ (-2 : ℝ) +
          K * Y * Real.log Y ^ (-2 : ℝ)) := by
    calc
      (1 - eps) * Y / Real.log Y = (1 - eps) * (Y / Real.log Y) := by ring
      _ ≤ (1 - eps / 2) * (Y / Real.log Y) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hratio.le
      _ = (1 - eps / 4) * (Y / Real.log Y) -
          eps / 4 * (Y / Real.log Y) := by ring
      _ ≤ Y / Real.log (2 * Y) -
          (K * (2 * Y) * Real.log (2 * Y) ^ (-2 : ℝ) +
            K * Y * Real.log Y ^ (-2 : ℝ)) := by
        linarith [hmain', herrBound]
  linarith [hcount, hli', htarget]

def reciprocalPrimeSum (Y : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo Y, 1 / (p : ℝ)

theorem primesUpTo_eq_Ioc (Y : ℝ) :
    primesUpTo Y = (Finset.Ioc 0 ⌊Y⌋₊).filter Nat.Prime := by
  ext p
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp, hY⟩, hprime⟩
    exact ⟨⟨by omega, hY⟩, hprime⟩
  · rintro ⟨⟨hp, hY⟩, hprime⟩
    exact ⟨⟨by omega, hY⟩, hprime⟩

theorem reciprocalPrimeSum_eq (Y : ℝ) :
    reciprocalPrimeSum Y = Real.log (Real.log Y) + Erdos970.Mertens.M +
      Erdos970.Mertens.E₂p Y := by
  unfold reciprocalPrimeSum
  rw [primesUpTo_eq_Ioc, Erdos970.Mertens.sum_prime_div_eq]

theorem prime_interval_reciprocal_sum (Y Z : ℝ)
    (hYZ : ⌊Y⌋₊ ≤ ⌊Z⌋₊) :
    (∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime, 1 / (p : ℝ)) =
      reciprocalPrimeSum Z - reciprocalPrimeSum Y := by
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
  have hsum := congrArg
    (fun s : Finset ℕ => ∑ p ∈ s.filter Nat.Prime, 1 / (p : ℝ)) hsplit
  rw [Finset.filter_union, Finset.sum_union hdis] at hsum
  have hsum' : reciprocalPrimeSum Z = reciprocalPrimeSum Y +
      (∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime, 1 / (p : ℝ)) := by
    simpa [reciprocalPrimeSum, primesUpTo] using hsum
  linarith

def scaledPrimeReciprocalInterval (x a b : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime, 1 / (p : ℝ)

theorem mertens_remainder_tendsto :
    Tendsto Erdos970.Mertens.E₂p atTop (nhds 0) :=
  (Asymptotics.isLittleO_one_iff ℝ).mp Erdos970.Mertens.E₂p.bound'

theorem scaledPrimeReciprocalInterval_tendsto {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x => scaledPrimeReciprocalInterval x a b)
      atTop (nhds (Real.log b - Real.log a)) := by
  have hb : 0 < b := ha.trans_le hab
  have haTop : Tendsto (fun x : ℝ => x ^ a) atTop atTop := tendsto_rpow_atTop ha
  have hbTop : Tendsto (fun x : ℝ => x ^ b) atTop atTop := tendsto_rpow_atTop hb
  let E₂ : ℝ → ℝ := Erdos970.Mertens.E₂p
  have hE₂ : Tendsto E₂ atTop (nhds 0) := by
    change Tendsto Erdos970.Mertens.E₂p atTop (nhds 0)
    exact mertens_remainder_tendsto
  have hEa := hE₂.comp haTop
  have hEb := hE₂.comp hbTop
  have hlogs : Tendsto
      (fun x : ℝ => Real.log (Real.log (x ^ b)) - Real.log (Real.log (x ^ a)))
      atTop (nhds (Real.log b - Real.log a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos hx
    rw [Real.log_rpow hx0 b, Real.log_rpow hx0 a,
      Real.log_mul hb.ne' hlogx.ne', Real.log_mul ha.ne' hlogx.ne']
    ring
  have hmodel : Tendsto
      (fun x : ℝ => Real.log (Real.log (x ^ b)) - Real.log (Real.log (x ^ a)) +
        E₂ (x ^ b) - E₂ (x ^ a))
      atTop (nhds (Real.log b - Real.log a)) := by
    simpa only [Function.comp_apply, sub_eq_add_neg, add_assoc, add_zero, neg_zero] using
      hlogs.add (hEb.sub hEa)
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hxpow : x ^ a ≤ x ^ b :=
    Real.rpow_le_rpow_of_exponent_le hx.le hab
  have hsum := prime_interval_reciprocal_sum (x ^ a) (x ^ b)
    (Nat.floor_mono hxpow)
  rw [scaledPrimeReciprocalInterval, hsum,
    reciprocalPrimeSum_eq (x ^ b), reciprocalPrimeSum_eq (x ^ a),
    Real.log_rpow hx0 b, Real.log_rpow hx0 a,
    Real.log_mul hb.ne' (Real.log_pos hx).ne',
    Real.log_mul ha.ne' (Real.log_pos hx).ne']
  ring

def DensityContinuityTask : Prop :=
  ContinuousOn (fun v : ℝ × ℝ => roughDensity v.1 v.2)
    {v | 0 < v.1 ∧ v.1 < v.2}

theorem densityTerm_scale {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {l : ℕ}
    (hl : 1 ≤ l) :
    densityTerm a (1 - a) l =
      (1 - a)⁻¹ * densityTerm (a / (1 - a)) 1 l := by
  let c : ℝ := 1 - a
  have hc : 0 < c := by dsimp [c]; linarith
  let F : (Fin (l - 1) → ℝ) → ℝ := fun s =>
    if (∀ i, a ≤ s i) ∧ (∑ i, s i) ≤ c - a then
      (c - ∑ i, s i)⁻¹ * ∏ i, (s i)⁻¹ else 0
  let G : (Fin (l - 1) → ℝ) → ℝ := fun t =>
    if (∀ i, a / c ≤ t i) ∧ (∑ i, t i) ≤ 1 - a / c then
      (1 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0
  have hcoords (t : Fin (l - 1) → ℝ) :
      (∀ i, a ≤ c * t i) ↔ ∀ i, a / c ≤ t i := by
    constructor
    · intro h i
      apply (div_le_iff₀ hc).2
      simpa [mul_comm] using h i
    · intro h i
      have hi := (div_le_iff₀ hc).1 (h i)
      simpa [mul_comm] using hi
  have hsum_eq (t : Fin (l - 1) → ℝ) :
      (∑ i, c * t i) = c * ∑ i, t i := by
    rw [Finset.mul_sum]
  have hratio : (c - a) / c = 1 - a / c := by
    field_simp [ne_of_gt hc]
    <;> ring
  have hsumcond (t : Fin (l - 1) → ℝ) :
      (∑ i, c * t i ≤ c - a) ↔ (∑ i, t i ≤ 1 - a / c) := by
    rw [hsum_eq, ← hratio]
    simpa [mul_comm] using (le_div_iff₀ hc).symm
  have hcond (t : Fin (l - 1) → ℝ) :
      ((∀ i, a ≤ c * t i) ∧ (∑ i, c * t i) ≤ c - a) ↔
        ((∀ i, a / c ≤ t i) ∧ (∑ i, t i) ≤ 1 - a / c) :=
    and_congr (hcoords t) (hsumcond t)
  have hprod (t : Fin (l - 1) → ℝ) :
      (∏ i, (c * t i)⁻¹) = (c⁻¹) ^ (l - 1) * ∏ i, (t i)⁻¹ := by
    calc
      (∏ i, (c * t i)⁻¹) = ∏ i, (c⁻¹ * (t i)⁻¹) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [mul_inv_rev, mul_comm]
      _ = (∏ _i : Fin (l - 1), c⁻¹) * ∏ i, (t i)⁻¹ := by
        rw [Finset.prod_mul_distrib]
      _ = (c⁻¹) ^ (l - 1) * ∏ i, (t i)⁻¹ := by simp
  have hden (t : Fin (l - 1) → ℝ) :
      c - ∑ i, c * t i = c * (1 - ∑ i, t i) := by
    rw [hsum_eq]
    ring
  have hlPow : (c⁻¹) ^ l = (c⁻¹) ^ (l - 1) * c⁻¹ := by
    conv_lhs => rw [show l = (l - 1) + 1 by omega]
    rw [pow_succ]
  have hpow : c⁻¹ * (c⁻¹) ^ (l - 1) = (c⁻¹) ^ l := by
    calc
      c⁻¹ * (c⁻¹) ^ (l - 1) = (c⁻¹) ^ (l - 1) * c⁻¹ := by ring
      _ = (c⁻¹) ^ l := hlPow.symm
  have hkernel (t : Fin (l - 1) → ℝ) :
      (c - ∑ i, c * t i)⁻¹ * ∏ i, (c * t i)⁻¹ =
        (c⁻¹) ^ l * ((1 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹) := by
    rw [hden t, hprod t, mul_inv_rev]
    calc
      (1 - ∑ i, t i)⁻¹ * c⁻¹ * ((c⁻¹) ^ (l - 1) * ∏ i, (t i)⁻¹) =
          (c⁻¹ * (c⁻¹) ^ (l - 1)) * ((1 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹) := by ring
      _ = (c⁻¹) ^ l * ((1 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹) := by rw [hpow]
  have hpoint (t : Fin (l - 1) → ℝ) :
      F (c • t) = (c⁻¹) ^ l * G t := by
    change (if (∀ i, a ≤ c * t i) ∧ (∑ i, c * t i) ≤ c - a then
        (c - ∑ i, c * t i)⁻¹ * ∏ i, (c * t i)⁻¹ else 0) =
      (c⁻¹) ^ l * (if (∀ i, a / c ≤ t i) ∧ (∑ i, t i) ≤ 1 - a / c then
        (1 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0)
    by_cases h : (∀ i, a / c ≤ t i) ∧ (∑ i, t i) ≤ 1 - a / c
    · have h' := hcond t |>.mpr h
      rw [if_pos h', if_pos h]
      exact hkernel t
    · have h' : ¬ ((∀ i, a ≤ c * t i) ∧ (∑ i, c * t i) ≤ c - a) :=
        fun hcnd => h (hcond t |>.mp hcnd)
      rw [if_neg h', if_neg h]
      simp
  have hscale := Measure.integral_comp_smul
    (μ := (volume : Measure (Fin (l - 1) → ℝ))) F c
  have hdim : Module.finrank ℝ (Fin (l - 1) → ℝ) = l - 1 := by simp
  have hscale' :
      (∫ t, F (c • t)) = (c ^ (l - 1))⁻¹ * ∫ t, F t := by
    simpa [hdim, smul_eq_mul, abs_of_pos (inv_pos.mpr (pow_pos hc _))] using hscale
  have hkernel_int :
      (∫ t, F (c • t)) = (c⁻¹) ^ l * ∫ t, G t := by
    calc
      (∫ t, F (c • t)) = ∫ t, (c⁻¹) ^ l * G t := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = (c⁻¹) ^ l * ∫ t, G t := by rw [integral_const_mul]
  have hEq : (c ^ (l - 1))⁻¹ * (∫ t, F t) =
      (c⁻¹) ^ l * ∫ t, G t := hscale'.symm.trans hkernel_int
  have hcancel : c ^ (l - 1) * (c⁻¹) ^ (l - 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hc.ne', one_pow]
  have hpowInv : c ^ (l - 1) * (c⁻¹) ^ l = c⁻¹ := by
    rw [hlPow]
    calc
      c ^ (l - 1) * ((c⁻¹) ^ (l - 1) * c⁻¹) =
          (c ^ (l - 1) * (c⁻¹) ^ (l - 1)) * c⁻¹ := by ring
      _ = c⁻¹ := by rw [hcancel]; ring
  have hfinal : (∫ t, F t) = c⁻¹ * ∫ t, G t := by
    calc
      (∫ t, F t) = c ^ (l - 1) * ((c ^ (l - 1))⁻¹ * ∫ t, F t) := by
        field_simp [ne_of_gt (pow_pos hc (l - 1))]
      _ = c ^ (l - 1) * ((c⁻¹) ^ l * ∫ t, G t) := congrArg
        (fun y : ℝ => c ^ (l - 1) * y) hEq
      _ = c⁻¹ * ∫ t, G t := by rw [← mul_assoc, hpowInv]
  change (∫ t, F t) = c⁻¹ * (∫ t, G t)
  exact hfinal

private def piSumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n, ContinuousLinearMap.proj i

private lemma measure_pi_sum_level_zero (n : ℕ) (hn : 0 < n) (c : ℝ) :
    volume {t : Fin n → ℝ | ∑ i, t i = c} = 0 := by
  let i : Fin n := ⟨0, hn⟩
  let v : Fin n → ℝ := Pi.single i c
  let A : AffineSubspace ℝ (Fin n → ℝ) := AffineSubspace.mk' v (piSumCLM n).toLinearMap.ker
  have hsumv : piSumCLM n v = c := by
    simp [piSumCLM, v]
  have hsumv' : (piSumCLM n).toLinearMap v = c := hsumv
  have hset : (A : Set (Fin n → ℝ)) = {t | ∑ j, t j = c} := by
    ext t
    change (piSumCLM n).toLinearMap (t - v) = 0 ↔ ∑ j, t j = c
    rw [map_sub, hsumv', sub_eq_zero]
    simp [piSumCLM]
  have hnot : (Pi.single i (c + 1) : Fin n → ℝ) ∉ A := by
    change (Pi.single i (c + 1) : Fin n → ℝ) ∉ (A : Set (Fin n → ℝ))
    rw [hset]
    simp [i]
  have hne : A ≠ ⊤ := by
    intro htop
    exact hnot (htop ▸ Set.mem_univ _)
  rw [← hset]
  exact Measure.addHaar_affineSubspace volume A hne

private lemma measure_pi_coordinate_level_zero (n : ℕ) (i : Fin n) (c : ℝ) :
    volume {t : Fin n → ℝ | t i = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i c

private def densityIntegrand (gamma w : ℝ) (l : ℕ) (t : Fin (l - 1) → ℝ) : ℝ :=
  if (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma then
    (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹
  else 0

private lemma densityIntegrand_measurable (gamma w : ℝ) (l : ℕ) :
    Measurable (densityIntegrand gamma w l) := by
  unfold densityIntegrand
  have hcond : MeasurableSet {t : Fin (l - 1) → ℝ |
      (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma} := by
    measurability
  exact Measurable.ite hcond (by fun_prop) measurable_const

private lemma densityBoundary_ae (gamma w : ℝ) (l : ℕ) (hl : 2 ≤ l) :
    ∀ᵐ t : Fin (l - 1) → ℝ, (∀ i, t i ≠ gamma) ∧ (∑ i, t i) ≠ w - gamma := by
  have hn : 0 < l - 1 := by omega
  have hcoord : ∀ i : Fin (l - 1), ∀ᵐ t : Fin (l - 1) → ℝ, t i ≠ gamma := by
    intro i
    rw [ae_iff]
    simpa [not_ne_iff] using measure_pi_coordinate_level_zero (l - 1) i gamma
  have hsum : ∀ᵐ t : Fin (l - 1) → ℝ, (∑ i, t i) ≠ w - gamma := by
    rw [ae_iff]
    simpa [not_ne_iff] using measure_pi_sum_level_zero (l - 1) hn (w - gamma)
  filter_upwards [ae_all_iff.2 hcoord, hsum] with t ht hs
  exact ⟨ht, hs⟩

private lemma densityIntegrand_tendsto {gamma w : ℝ} {l : ℕ} {p : ℕ → ℝ × ℝ}
    {t : Fin (l - 1) → ℝ}
    (hgamma_pos : 0 < gamma)
    (hgamma : Tendsto (fun n => (p n).1) atTop (nhds gamma))
    (hw : Tendsto (fun n => (p n).2) atTop (nhds w))
    (hcoord : ∀ i, t i ≠ gamma) (hsum : (∑ i, t i) ≠ w - gamma) :
    Tendsto (fun n => densityIntegrand (p n).1 (p n).2 l t) atTop
      (nhds (densityIntegrand gamma w l t)) := by
  let P : ℕ → Prop := fun n =>
    (∀ i, (p n).1 ≤ t i) ∧ (∑ i, t i) ≤ (p n).2 - (p n).1
  let P₀ : Prop := (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma
  have hright : Tendsto (fun n => (p n).2 - (p n).1) atTop (nhds (w - gamma)) :=
    hw.sub hgamma
  have hcoord_stable : ∀ i, ∀ᶠ n in atTop, ((p n).1 ≤ t i) ↔ (gamma ≤ t i) := by
    intro i
    rcases lt_or_gt_of_ne (Ne.symm (hcoord i)) with hlt | hgt
    · filter_upwards [hgamma.eventually (Iio_mem_nhds hlt)] with n hn
      exact iff_of_true hn.le hlt.le
    · filter_upwards [hgamma.eventually (Ioi_mem_nhds hgt)] with n hn
      exact iff_of_false (not_le_of_gt hn) (not_le_of_gt hgt)
  have hcoords_stable : ∀ᶠ n in atTop, (∀ i, (p n).1 ≤ t i) ↔ (∀ i, gamma ≤ t i) := by
    filter_upwards [eventually_all.2 hcoord_stable] with n hn
    constructor
    · intro h i
      exact (hn i).mp (h i)
    · intro h i
      exact (hn i).mpr (h i)
  have hsum_stable : ∀ᶠ n in atTop,
      ((∑ i, t i) ≤ (p n).2 - (p n).1) ↔ ((∑ i, t i) ≤ w - gamma) := by
    rcases lt_or_gt_of_ne hsum with hlt | hgt
    · filter_upwards [hright.eventually (Ioi_mem_nhds hlt)] with n hn
      exact iff_of_true hn.le hlt.le
    · filter_upwards [hright.eventually (Iio_mem_nhds hgt)] with n hn
      exact iff_of_false (not_le_of_gt hn) (not_le_of_gt hgt)
  have hP_stable : ∀ᶠ n in atTop, P n ↔ P₀ := by
    filter_upwards [hcoords_stable, hsum_stable] with n hc hs
    change ((∀ i, (p n).1 ≤ t i) ∧ (∑ i, t i) ≤ (p n).2 - (p n).1) ↔
      ((∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma)
    exact and_congr hc hs
  by_cases hP₀ : P₀
  · have hP : ∀ᶠ n in atTop, P n := hP_stable.mono fun n hn => hn.mpr hP₀
    have hden : 0 < w - ∑ i, t i := by
      linarith [hP₀.2, hgamma_pos]
    have hden_tendsto : Tendsto (fun n => (p n).2 - ∑ i, t i) atTop
        (nhds (w - ∑ i, t i)) := by
      simpa using hw.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑ i, t i) atTop
        (nhds (∑ i, t i)))
    have hinv := hden_tendsto.inv₀ (ne_of_gt hden)
    have hformula : Tendsto
        (fun n => ((p n).2 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹) atTop
        (nhds ((w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹)) := by
      simpa using hinv.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => ∏ i, (t i)⁻¹) atTop (nhds (∏ i, (t i)⁻¹)))
    have heq : (fun n => densityIntegrand (p n).1 (p n).2 l t) =ᶠ[atTop]
        fun n => ((p n).2 - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ := by
      filter_upwards [hP] with n hn
      simp [densityIntegrand, P, hn]
    have htarget : densityIntegrand gamma w l t =
        (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ := by
      simp [densityIntegrand, P₀, hP₀]
    rw [htarget]
    exact hformula.congr' heq.symm
  · have hnotP : ∀ᶠ n in atTop, ¬ P n :=
      hP_stable.mono fun n hn h => hP₀ (hn.mp h)
    have heq : (fun n => densityIntegrand (p n).1 (p n).2 l t) =ᶠ[atTop]
        fun _ => (0 : ℝ) := by
      filter_upwards [hnotP] with n hn
      simp [densityIntegrand, P, hn]
    have htarget : densityIntegrand gamma w l t = 0 := by
      simp [densityIntegrand, P₀, hP₀]
    rw [htarget]
    exact tendsto_const_nhds.congr' heq.symm

private lemma densityIntegrand_support_ball {gamma w : ℝ} {l : ℕ}
    {gamma' w' : ℝ} {t : Fin (l - 1) → ℝ}
    (hgamma : 0 < gamma) (hgamma' : gamma / 2 < gamma') (hw' : w' < w + 1)
    (hdom : (∀ i, gamma' ≤ t i) ∧ (∑ i, t i) ≤ w' - gamma') :
    t ∈ Metric.closedBall (0 : Fin (l - 1) → ℝ) (w + 1) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have hgamma'_pos : 0 < gamma' := by linarith
  have hsum_nonneg : 0 ≤ ∑ j, t j :=
    Finset.sum_nonneg fun j hj => (le_of_lt hgamma'_pos).trans (hdom.1 j)
  have hw'_pos : 0 < w' := by linarith [hdom.2]
  apply (pi_norm_le_iff_of_nonneg (by linarith)).2
  intro i
  have hti_pos : 0 < t i := lt_of_lt_of_le hgamma'_pos (hdom.1 i)
  have hsum_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin (l - 1))), 0 ≤ t j :=
    fun j _ => (le_of_lt hgamma'_pos).trans (hdom.1 j)
  have hti_sum : t i ≤ ∑ j, t j :=
    Finset.single_le_sum hsum_nonneg (Finset.mem_univ i)
  have hti_le : t i ≤ w + 1 := by linarith [hdom.2, hti_sum]
  rw [Real.norm_eq_abs, abs_of_nonneg hti_pos.le]
  exact hti_le

private lemma densityIntegrand_norm_bound {gamma : ℝ} {l : ℕ}
    {gamma' w' : ℝ} {t : Fin (l - 1) → ℝ} (hl : 2 ≤ l)
    (hgamma : 0 < gamma) (hgamma' : gamma / 2 < gamma')
    (hdom : (∀ i, gamma' ≤ t i) ∧ (∑ i, t i) ≤ w' - gamma') :
    ‖densityIntegrand gamma' w' l t‖ ≤ (gamma / 2)⁻¹ ^ l := by
  have hbase : 0 < gamma / 2 := by linarith
  have hbase_inv : (gamma / 2)⁻¹ = 2 / gamma := by
    field_simp [ne_of_gt hgamma]
  have hden : gamma / 2 ≤ w' - ∑ i, t i := by linarith [hdom.2]
  have hden_pos : 0 < w' - ∑ i, t i := hbase.trans_le hden
  have hden_inv : (w' - ∑ i, t i)⁻¹ ≤ 2 / gamma := by
    simpa [hbase_inv] using (one_div_le_one_div_of_le hbase hden)
  have hti_pos : ∀ i, 0 < t i := fun i => (by linarith [hgamma', hdom.1 i])
  have hti_inv : ∀ i, 0 ≤ (t i)⁻¹ ∧ (t i)⁻¹ ≤ 2 / gamma := by
    intro i
    constructor
    · exact inv_nonneg.mpr (le_of_lt (hti_pos i))
    · have hi : gamma / 2 ≤ t i := by linarith [hgamma', hdom.1 i]
      simpa [hbase_inv] using (one_div_le_one_div_of_le hbase hi)
  have hprod : (∏ i, (t i)⁻¹) ≤ (2 / gamma) ^ (l - 1) := by
    calc
      (∏ i, (t i)⁻¹) ≤ ∏ _i : Fin (l - 1), (2 / gamma) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (hti_inv i).1
        · intro i hi
          exact (hti_inv i).2
      _ = (2 / gamma) ^ (l - 1) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod_nonneg : 0 ≤ ∏ i, (t i)⁻¹ :=
    Finset.prod_nonneg fun i hi => (hti_inv i).1
  have hkernel_nonneg : 0 ≤ (w' - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hden_pos.le) hprod_nonneg
  rw [densityIntegrand, if_pos hdom, Real.norm_eq_abs, abs_of_nonneg hkernel_nonneg]
  calc
    (w' - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ ≤
    (2 / gamma) * (2 / gamma) ^ (l - 1) :=
      mul_le_mul hden_inv hprod hprod_nonneg (by positivity)
    _ = (2 / gamma) ^ l := by
      rw [show l = (l - 1) + 1 by omega, pow_succ']
      rw [show l - 1 + 1 - 1 = l - 1 by omega]
    _ = (gamma / 2)⁻¹ ^ l := by rw [hbase_inv]

private lemma densityTerm_tendsto {gamma w : ℝ} {l : ℕ} {p : ℕ → ℝ × ℝ}
    (hgamma_pos : 0 < gamma) (hl : 2 ≤ l)
    (hp : Tendsto p atTop (nhds (gamma, w))) :
    Tendsto (fun n => densityTerm (p n).1 (p n).2 l) atTop (nhds (densityTerm gamma w l)) := by
  have hgamma : Tendsto (fun n => (p n).1) atTop (nhds gamma) := by
    change Tendsto (Prod.fst ∘ p) atTop (nhds gamma)
    exact (continuous_fst.tendsto (gamma, w)).comp hp
  have hw : Tendsto (fun n => (p n).2) atTop (nhds w) := by
    change Tendsto (Prod.snd ∘ p) atTop (nhds w)
    exact (continuous_snd.tendsto (gamma, w)).comp hp
  let K : Set (Fin (l - 1) → ℝ) := Metric.closedBall 0 (w + 1)
  let C : ℝ := (2 / gamma) ^ l
  let bound : (Fin (l - 1) → ℝ) → ℝ := K.indicator (fun _ => C)
  have hbound_int : Integrable bound volume := by
    have hK : volume K ≠ ⊤ := (isCompact_closedBall (0 : Fin (l - 1) → ℝ) (w + 1)).measure_ne_top
    exact (integrableOn_const (μ := volume) (s := K) (C := C) hK).integrable_indicator
      (Metric.isClosed_closedBall.measurableSet)
  have hgamma_event : ∀ᶠ n in atTop, gamma / 2 < (p n).1 :=
    hgamma.eventually (Ioi_mem_nhds (by linarith))
  have hw_event : ∀ᶠ n in atTop, (p n).2 < w + 1 :=
    hw.eventually (Iio_mem_nhds (by linarith))
  have hparameter_event : ∀ᶠ n in atTop,
      gamma / 2 < (p n).1 ∧ (p n).2 < w + 1 := hgamma_event.and hw_event
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun t : Fin (l - 1) → ℝ => densityIntegrand (p n).1 (p n).2 l t) volume :=
    Filter.Eventually.of_forall fun n => (densityIntegrand_measurable _ _ _).aestronglyMeasurable
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t : Fin (l - 1) → ℝ, ‖densityIntegrand (p n).1 (p n).2 l t‖ ≤ bound t := by
    filter_upwards [hparameter_event] with n hn
    apply ae_of_all
    intro t
    by_cases hdom : (∀ i, (p n).1 ≤ t i) ∧ (∑ i, t i) ≤ (p n).2 - (p n).1
    · have htK : t ∈ K := densityIntegrand_support_ball hgamma_pos hn.1 hn.2 hdom
      simpa [bound, K, C, htK] using
        densityIntegrand_norm_bound hl hgamma_pos hn.1 hdom
    · by_cases htK : t ∈ K
      · simp [densityIntegrand, bound, K, C, hdom, htK]
        positivity
      · simp [densityIntegrand, bound, K, C, hdom, htK]
  have hlim : ∀ᵐ t : Fin (l - 1) → ℝ, Tendsto
      (fun n => densityIntegrand (p n).1 (p n).2 l t) atTop (nhds (densityIntegrand gamma w l t)) := by
    filter_upwards [densityBoundary_ae gamma w l hl] with t ht
    exact densityIntegrand_tendsto hgamma_pos hgamma hw ht.1 ht.2
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) bound hmeas hbound hbound_int hlim
  simpa [densityTerm, densityIntegrand] using hDCT

private lemma densityTerm_zero_of_lt {gamma w : ℝ} {l : ℕ}
    (hgamma : 0 < gamma) (hl : 2 ≤ l) (hsize : w < (l : ℝ) * gamma) :
    densityTerm gamma w l = 0 := by
  have hzero : ∀ t : Fin (l - 1) → ℝ, densityIntegrand gamma w l t = 0 := by
    intro t
    by_cases hdom : (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma
    · have hcastNat : l - 1 + 1 = l := Nat.sub_add_cancel (by omega : 1 ≤ l)
      have hcast : ((l - 1 : ℕ) : ℝ) + 1 = (l : ℝ) := by exact_mod_cast hcastNat
      have hlow : (l - 1 : ℝ) * gamma ≤ ∑ i, t i := by
        calc
          (l - 1 : ℝ) * gamma = ((l - 1 : ℕ) : ℝ) * gamma := by
            congr 1
            linarith [hcast]
          _ = ∑ _i : Fin (l - 1), gamma := by simp
          _ ≤ ∑ i, t i := Finset.sum_le_sum fun i hi => hdom.1 i
      have hcontra : (l : ℝ) * gamma ≤ w := by nlinarith [hdom.2, hlow, hcast]
      exact (False.elim ((not_lt_of_ge hcontra) hsize))
    · simp [densityIntegrand, hdom]
  change (∫ t : Fin (l - 1) → ℝ, densityIntegrand gamma w l t) = 0
  rw [show (fun t : Fin (l - 1) → ℝ => densityIntegrand gamma w l t) = fun _ => 0 from
    funext hzero]
  simp

private lemma roughDensity_eq_cutoff (gamma w : ℝ) (hgamma : 0 < gamma)
    (N : ℕ) (hcut : ⌊w / gamma⌋₊ ≤ N) :
    roughDensity gamma w = w⁻¹ +
      ∑ l ∈ Finset.Icc 2 N, densityTerm gamma w l / (l.factorial : ℝ) := by
  unfold roughDensity
  apply congrArg (fun x : ℝ => w⁻¹ + x)
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hcut)
  intro l hl hnot
  have hlower : 2 ≤ l := (Finset.mem_Icc.mp hl).1
  have hfloor_lt : ⌊w / gamma⌋₊ < l := by
    by_contra h
    have hmem : l ∈ Finset.Icc 2 ⌊w / gamma⌋₊ := Finset.mem_Icc.mpr ⟨hlower, le_of_not_gt h⟩
    exact hnot hmem
  have hratio : w / gamma < l := Nat.lt_of_floor_lt hfloor_lt
  have hsize : w < (l : ℝ) * gamma := (div_lt_iff₀ hgamma).mp hratio
  simp [densityTerm_zero_of_lt hgamma hlower hsize]

private lemma roughDensity_tendsto {gamma w : ℝ} {p : ℕ → ℝ × ℝ}
    (hgamma : 0 < gamma) (hw : gamma < w)
    (hseq : ∀ n, 0 < (p n).1 ∧ (p n).1 < (p n).2)
    (hp : Tendsto p atTop (nhds (gamma, w))) :
    Tendsto (fun n => roughDensity (p n).1 (p n).2) atTop
      (nhds (roughDensity gamma w)) := by
  have hgamma_tendsto : Tendsto (fun n => (p n).1) atTop (nhds gamma) := by
    change Tendsto (Prod.fst ∘ p) atTop (nhds gamma)
    exact (continuous_fst.tendsto (gamma, w)).comp hp
  have hw_tendsto : Tendsto (fun n => (p n).2) atTop (nhds w) := by
    change Tendsto (Prod.snd ∘ p) atTop (nhds w)
    exact (continuous_snd.tendsto (gamma, w)).comp hp
  have hratio_tendsto : Tendsto (fun n => (p n).2 / (p n).1) atTop (nhds (w / gamma)) :=
    hw_tendsto.div hgamma_tendsto (ne_of_gt hgamma)
  obtain ⟨N, hN⟩ := exists_nat_gt (w / gamma)
  let M : ℕ := max 2 N
  have hM2 : 2 ≤ M := by simp [M]
  have hMreal : w / gamma < (M : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast (Nat.le_max_right 2 N))
  have hratio_event : ∀ᶠ n in atTop, (p n).2 / (p n).1 < M :=
    hratio_tendsto.eventually (Iio_mem_nhds hMreal)
  have hsum_tendsto : Tendsto
      (fun n => ∑ l ∈ Finset.Icc 2 M,
        densityTerm (p n).1 (p n).2 l / (l.factorial : ℝ)) atTop
      (nhds (∑ l ∈ Finset.Icc 2 M, densityTerm gamma w l / (l.factorial : ℝ))) := by
    apply tendsto_finsetSum
    intro l hl
    have hl2 : 2 ≤ l := (Finset.mem_Icc.mp hl).1
    simpa [div_eq_mul_inv] using
      (densityTerm_tendsto hgamma hl2 hp).mul_const ((l.factorial : ℝ)⁻¹)
  have hwinv : Tendsto (fun n => ((p n).2)⁻¹) atTop (nhds (w⁻¹)) :=
    hw_tendsto.inv₀ (ne_of_gt (lt_trans hgamma hw))
  have hfinite : Tendsto
      (fun n => ((p n).2)⁻¹ + ∑ l ∈ Finset.Icc 2 M,
        densityTerm (p n).1 (p n).2 l / (l.factorial : ℝ)) atTop
      (nhds (w⁻¹ + ∑ l ∈ Finset.Icc 2 M,
        densityTerm gamma w l / (l.factorial : ℝ))) := hwinv.add hsum_tendsto
  have hevent_eq : (fun n => ((p n).2)⁻¹ + ∑ l ∈ Finset.Icc 2 M,
      densityTerm (p n).1 (p n).2 l / (l.factorial : ℝ)) =ᶠ[atTop]
      fun n => roughDensity (p n).1 (p n).2 := by
    filter_upwards [hratio_event] with n hn
    have hrpos : 0 < (p n).2 / (p n).1 :=
      div_pos (lt_trans (hseq n).1 (hseq n).2) (hseq n).1
    have hfloor : ⌊(p n).2 / (p n).1⌋₊ < M :=
      (Nat.floor_lt hrpos.le).2 hn
    exact (roughDensity_eq_cutoff (p n).1 (p n).2 (hseq n).1 M hfloor.le).symm
  have htarget_floor : ⌊w / gamma⌋₊ ≤ M := by
    have hrpos : 0 < w / gamma := div_pos (lt_trans hgamma hw) hgamma
    exact ((Nat.floor_lt hrpos.le).2 hMreal).le
  have htarget_eq := roughDensity_eq_cutoff gamma w hgamma M htarget_floor
  rw [htarget_eq]
  exact hfinite.congr' hevent_eq

theorem densityContinuityTask_proof : DensityContinuityTask := by
  rw [DensityContinuityTask, continuousOn_iff_continuous_domRestrict]
  apply (continuous_iff_seqContinuous).2
  intro p q hp
  change Tendsto (fun n => roughDensity (p n).val.1 (p n).val.2) atTop
    (nhds (roughDensity q.val.1 q.val.2))
  have hpval : Tendsto (fun n => (p n).val) atTop (nhds q.val) :=
    (continuous_subtype_val.tendsto q).comp hp
  exact roughDensity_tendsto q.property.1 q.property.2
    (fun n => (p n).property) hpval

theorem roughDensity_scale {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    roughDensity a (1 - a) = (1 - a)⁻¹ * roughDensity (a / (1 - a)) 1 := by
  let c : ℝ := 1 - a
  let N : ℕ := ⌊c / a⌋₊
  have hc : 0 < c := by dsimp [c]; linarith
  have hgamma : 0 < a / c := div_pos ha hc
  have hfloorA : ⌊(1 - a) / a⌋₊ = N := by simp [N, c]
  have hratio : 1 / (a / c) = c / a := by field_simp [ne_of_gt ha, ne_of_gt hc]
  have hfloorB : ⌊1 / (a / c)⌋₊ = N := by rw [hratio]
  rw [roughDensity_eq_cutoff a (1 - a) ha N (by rw [hfloorA]),
      roughDensity_eq_cutoff (a / c) 1 hgamma N (by rw [hfloorB])]
  have hterm : ∀ l ∈ Finset.Icc 2 N,
      densityTerm a (1 - a) l / (l.factorial : ℝ) =
        c⁻¹ * (densityTerm (a / c) 1 l / (l.factorial : ℝ)) := by
    intro l hl
    have hl1 : 1 ≤ l := by have := (Finset.mem_Icc.mp hl).1; omega
    rw [densityTerm_scale ha (by linarith [ha2]) hl1]
    ring
  have hsum :
      (∑ l ∈ Finset.Icc 2 N, densityTerm a (1 - a) l / (l.factorial : ℝ)) =
        c⁻¹ * ∑ l ∈ Finset.Icc 2 N,
          densityTerm (a / c) 1 l / (l.factorial : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact hterm l hl
  rw [hsum]
  dsimp [c]
  ring

lemma densityTerm_nonneg {gamma w : ℝ} (hgamma : 0 ≤ gamma) (l : ℕ) :
    0 ≤ densityTerm gamma w l := by
  change 0 ≤ ∫ t : Fin (l - 1) → ℝ,
    (if (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma then
      (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0)
  apply integral_nonneg
  intro t
  change 0 ≤ (if (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma then
    (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0)
  split_ifs with h
  · obtain ⟨hcoord, hsum⟩ := h
    have hden : 0 ≤ w - ∑ i, t i := by linarith
    have hprod : 0 ≤ ∏ i, (t i)⁻¹ :=
      Finset.prod_nonneg fun i hi => inv_nonneg.mpr (le_trans hgamma (hcoord i))
    exact mul_nonneg (inv_nonneg.mpr hden) hprod
  · exact le_rfl

lemma roughDensity_one_ge_one {gamma : ℝ} (hgamma : 0 < gamma) :
    1 ≤ roughDensity gamma 1 := by
  unfold roughDensity
  rw [inv_one]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro l hl
  apply div_nonneg (densityTerm_nonneg hgamma.le l)
  positivity

lemma densityTerm_eq (gamma w : ℝ) (l : ℕ) :
    densityTerm gamma w l =
      ∫ t : Fin (l - 1) → ℝ, densityIntegrand gamma w l t := rfl

lemma densityTerm_zero_of_le {gamma w : ℝ} (hgamma : 0 < gamma) {l : ℕ}
    (hl : 2 ≤ l) (hsize : w ≤ (l : ℝ) * gamma) : densityTerm gamma w l = 0 := by
  rw [densityTerm_eq]
  apply integral_eq_zero_of_ae
  filter_upwards [densityBoundary_ae gamma w l hl] with t ht
  by_cases hd : (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma
  · have hlow : ((l - 1 : ℕ) : ℝ) * gamma ≤ ∑ i, t i := by
      calc
        ((l - 1 : ℕ) : ℝ) * gamma = ∑ _i : Fin (l - 1), gamma := by simp
        _ ≤ ∑ i, t i := Finset.sum_le_sum fun i hi => hd.1 i
    have hlcast : ((l - 1 : ℕ) : ℝ) + 1 = (l : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ l))
    have hsum : (∑ i, t i) = w - gamma := by nlinarith [hlow, hd.2, hsize, hlcast]
    exact False.elim (ht.2 hsum)
  · simp [densityIntegrand, hd]

lemma roughDensity_eq_one_of_half_lt {b : ℝ} (hb2 : 1 / 2 < b) (hb1 : b < 1) :
    roughDensity b 1 = 1 := by
  have hb : 0 < b := by linarith
  have hlow : 1 ≤ 1 / b := (le_div_iff₀ hb).2 (by nlinarith)
  have hratio_pos : 0 < 1 / b := by positivity
  have hupp : 1 / b < 2 := by
    rw [div_lt_iff₀ hb]
    linarith
  have hfloor_lt : ⌊1 / b⌋₊ < 2 := (Nat.floor_lt hratio_pos.le).2 hupp
  have hlow' : (1 : ℝ) ≤ 1 / b := hlow
  have hfloor_ge : 1 ≤ ⌊1 / b⌋₊ := Nat.le_floor (by exact_mod_cast hlow')
  have hfloor : ⌊1 / b⌋₊ = 1 := by omega
  rw [roughDensity_eq_cutoff b 1 hb 1 (by rw [hfloor])]
  simp

lemma roughDensity_eq_one_of_ge_half {b : ℝ} (hb2 : 1 / 2 ≤ b) (hb1 : b < 1) :
    roughDensity b 1 = 1 := by
  by_cases hstrict : 1 / 2 < b
  · exact roughDensity_eq_one_of_half_lt hstrict hb1
  · have hbEq : b = 1 / 2 := by linarith
    have hb : 0 < b := by linarith
    have hfloor : ⌊1 / b⌋₊ = 2 := by rw [hbEq]; norm_num
    rw [roughDensity_eq_cutoff b 1 hb 2 (by rw [hfloor])]
    have hterm : densityTerm b 1 2 = 0 := by
      rw [hbEq]
      apply densityTerm_zero_of_le (by norm_num) (by norm_num)
      norm_num
    simp [hterm]

lemma roughDensity_eq_inv_one_sub {a : ℝ} (ha : 1 / 3 < a) (ha2 : a ≤ 1 / 2) :
    roughDensity a (1 - a) = (1 - a)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hratioLo : 1 ≤ (1 - a) / a := by
    apply (le_div_iff₀ ha0).2
    linarith
  have hratioHi : (1 - a) / a < 2 := by
    apply (div_lt_iff₀ ha0).2
    linarith
  have hratioPos : 0 < (1 - a) / a := by positivity
  have hfloorLt : ⌊(1 - a) / a⌋₊ < 2 := (Nat.floor_lt hratioPos.le).2 hratioHi
  have hfloorGe : 1 ≤ ⌊(1 - a) / a⌋₊ :=
    Nat.le_floor (by exact_mod_cast hratioLo)
  have hfloor : ⌊(1 - a) / a⌋₊ = 1 := by omega
  rw [roughDensity_eq_cutoff a (1 - a) ha0 1 (by rw [hfloor])]
  simp

def leastFactorDensity (a : ℝ) : ℝ :=
  roughDensity (a / (1 - a)) 1 / (1 - a)

lemma leastFactorDensity_continuousOn {b B : ℝ} (hb : 0 < b) (hB : B < 1 / 2)
    (hbB : b ≤ B) : ContinuousOn leastFactorDensity (Set.Icc b B) := by
  let K : Set ℝ := Set.Icc b B
  have hdenPos : ∀ a ∈ K, 0 < 1 - a := by
    intro a ha
    have haB := (Set.mem_Icc.mp ha).2
    linarith
  have hinv : ContinuousOn (fun a : ℝ => (1 - a)⁻¹) K := by
    apply (continuousOn_const.sub continuousOn_id).inv₀
    intro a ha
    exact ne_of_gt (hdenPos a ha)
  have hphi : ContinuousOn (fun a : ℝ => a / (1 - a)) K := by
    have hphi' : ContinuousOn (fun a : ℝ => a * (1 - a)⁻¹) K := by
      change ContinuousOn (fun a : ℝ => a * (1 - a)⁻¹) K
      exact continuousOn_id.mul hinv
    simpa only [div_eq_mul_inv] using hphi'
  have hmapCont : ContinuousOn (fun a : ℝ => (a / (1 - a), (1 : ℝ))) K :=
    hphi.prodMk continuousOn_const
  have hmap : Set.MapsTo (fun a : ℝ => (a / (1 - a), (1 : ℝ))) K
      {v : ℝ × ℝ | 0 < v.1 ∧ v.1 < v.2} := by
    intro a ha
    have haIcc := Set.mem_Icc.mp ha
    have hapos : 0 < a := lt_of_lt_of_le hb haIcc.1
    have hphiPos : 0 < a / (1 - a) := div_pos hapos (hdenPos a ha)
    have hphiLt : a / (1 - a) < 1 := by
      apply (div_lt_one (hdenPos a ha)).2
      have : a < 1 / 2 := lt_of_le_of_lt haIcc.2 hB
      linarith
    exact ⟨hphiPos, by simpa using hphiLt⟩
  have hjoint := densityContinuityTask_proof
  have hD : ContinuousOn (fun a : ℝ => roughDensity (a / (1 - a)) 1) K := by
    exact hjoint.comp hmapCont hmap
  change ContinuousOn (fun a : ℝ => roughDensity (a / (1 - a)) 1 / (1 - a)) K
  exact hD.div (continuousOn_const.sub continuousOn_id) (fun a ha => ne_of_gt (hdenPos a ha))

lemma densityKernel_scale {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    roughDensity a (1 - a) / a = leastFactorDensity a / a := by
  rw [roughDensity_scale ha ha2]
  unfold leastFactorDensity
  field_simp [ne_of_gt ha, ne_of_gt (by linarith : 0 < 1 - a)]
  <;> ring

lemma tail_density_integral_le {B : ℝ} (hB : 1 / 3 < B) (hBhalf : B < 1 / 2) :
    (∫ a : ℝ in B..(1 / 2 : ℝ), roughDensity a (1 - a) / a) ≤
      6 * (1 / 2 - B) := by
  let f : ℝ → ℝ := fun a => roughDensity a (1 - a) / a
  let g : ℝ → ℝ := fun a => (a * (1 - a))⁻¹
  have hEq : Set.EqOn f g (Set.uIcc B (1 / 2 : ℝ)) := by
    intro a ha
    have haIcc : a ∈ Set.Icc B (1 / 2 : ℝ) := by
      rw [Set.uIcc_of_le hBhalf.le] at ha
      exact ha
    have hB_le : B ≤ a := haIcc.1
    have haHalf : a ≤ 1 / 2 := haIcc.2
    have haThird : 1 / 3 < a := lt_of_lt_of_le hB hB_le
    rw [show f a = roughDensity a (1 - a) / a by rfl,
      roughDensity_eq_inv_one_sub haThird haHalf]
    dsimp [g]
    field_simp [ne_of_gt (by linarith : 0 < a), ne_of_gt (by linarith : 0 < 1 - a)]
    <;> ring
  have hcont : ContinuousOn g (Set.Icc B (1 / 2 : ℝ)) := by
    apply (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).inv₀
    intro a ha
    apply ne_of_gt
    have haPos : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 1 / 3) (lt_of_lt_of_le hB ha.1)
    have h1aPos : 0 < 1 - a := by linarith [ha.2]
    exact mul_pos haPos h1aPos
  have hgint : IntervalIntegrable g volume B (1 / 2 : ℝ) :=
    hcont.intervalIntegrable_of_Icc hBhalf.le
  have hconst : IntervalIntegrable (fun _ : ℝ => (6 : ℝ)) volume B (1 / 2 : ℝ) :=
    continuousOn_const.intervalIntegrable_of_Icc hBhalf.le
  have hmono : (∫ a : ℝ in B..(1 / 2 : ℝ), g a) ≤
      ∫ a : ℝ in B..(1 / 2 : ℝ), (6 : ℝ) := by
    apply intervalIntegral.integral_mono_on hBhalf.le hgint hconst
    intro a ha
    have haPos : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 1 / 3) (lt_of_lt_of_le hB ha.1)
    have h1a : 1 / 2 ≤ 1 - a := by linarith [ha.2]
    have haThird : 1 / 3 < a := lt_of_lt_of_le hB ha.1
    have hprod1 : (1 / 3 : ℝ) * (1 / 2) ≤ (1 / 3) * (1 - a) :=
      mul_le_mul_of_nonneg_left h1a (by norm_num)
    have hprod2 : (1 / 3 : ℝ) * (1 - a) ≤ a * (1 - a) :=
      mul_le_mul_of_nonneg_right haThird.le (by linarith [ha.1, hB])
    have hprod : 1 / 6 ≤ a * (1 - a) := by nlinarith [hprod1, hprod2]
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 6) hprod
    simpa [g, one_div] using hinv
  have hcongr : (∫ a : ℝ in B..(1 / 2 : ℝ), f a) =
      ∫ a : ℝ in B..(1 / 2 : ℝ), g a := by
    apply intervalIntegral.integral_congr
    exact hEq
  calc
    (∫ a : ℝ in B..(1 / 2 : ℝ), f a) =
        ∫ a : ℝ in B..(1 / 2 : ℝ), g a := hcongr
    _ ≤ ∫ a : ℝ in B..(1 / 2 : ℝ), (6 : ℝ) := hmono
    _ = 6 * (1 / 2 - B) := by simp [smul_eq_mul] <;> ring

lemma densityIntegral_split {b B : ℝ} (hb : 0 < b) (hbB : b < B)
    (hBthird : 1 / 3 < B) (hB : B < 1 / 2) :
    (∫ a : ℝ in b..(1 / 2 : ℝ), roughDensity a (1 - a) / a) =
      (∫ a : ℝ in b..B, leastFactorDensity a / a) +
        (∫ a : ℝ in B..(1 / 2 : ℝ), roughDensity a (1 - a) / a) := by
  let f : ℝ → ℝ := fun a => roughDensity a (1 - a) / a
  let g : ℝ → ℝ := fun a => leastFactorDensity a / a
  have hBpos : 0 < B := lt_trans hb hbB
  have hGcont : ContinuousOn leastFactorDensity (Set.Icc b B) :=
    leastFactorDensity_continuousOn hb hB (le_of_lt hbB)
  have hgcont : ContinuousOn g (Set.Icc b B) := by
    apply hGcont.div continuousOn_id
    intro a ha
    exact ne_of_gt (lt_of_lt_of_le hb (Set.mem_Icc.mp ha).1)
  have hsmallEq : Set.EqOn f g (Set.Icc b B) := by
    intro a ha
    have ha0 : 0 < a := lt_of_lt_of_le hb (Set.mem_Icc.mp ha).1
    have haHalf : a < 1 / 2 := lt_of_le_of_lt (Set.mem_Icc.mp ha).2 hB
    dsimp [f, g]
    exact densityKernel_scale ha0 haHalf
  have hsmallFCont : ContinuousOn f (Set.Icc b B) := hgcont.congr hsmallEq
  have hsmallInt : IntervalIntegrable f volume b B :=
    hsmallFCont.intervalIntegrable_of_Icc hbB.le
  have htailCont : ContinuousOn (fun a : ℝ => (a * (1 - a))⁻¹)
      (Set.Icc B (1 / 2 : ℝ)) := by
    apply (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).inv₀
    intro a ha
    have ha0 : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 1 / 3)
      (lt_of_lt_of_le hBthird ha.1)
    have h1a : 0 < 1 - a := by linarith [ha.2]
    exact ne_of_gt (mul_pos ha0 h1a)
  have htailEq : Set.EqOn f (fun a : ℝ => (a * (1 - a))⁻¹)
      (Set.Icc B (1 / 2 : ℝ)) := by
    intro a ha
    have haThird : 1 / 3 < a := lt_of_lt_of_le hBthird ha.1
    have haHalf : a ≤ 1 / 2 := ha.2
    have haPos : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 1 / 3) haThird
    have h1aPos : 0 < 1 - a := by linarith [haHalf]
    dsimp [f]
    rw [roughDensity_eq_inv_one_sub haThird haHalf]
    field_simp [ne_of_gt haPos, ne_of_gt h1aPos]
    <;> ring
  have htailFCont : ContinuousOn f (Set.Icc B (1 / 2 : ℝ)) :=
    htailCont.congr htailEq
  have htailInt : IntervalIntegrable f volume B (1 / 2 : ℝ) :=
    htailFCont.intervalIntegrable_of_Icc (le_of_lt hB)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hsmallInt htailInt
  have hsmallIntegral : (∫ a : ℝ in b..B, f a) = ∫ a : ℝ in b..B, g a := by
    have hEqU : Set.EqOn f g (Set.uIcc b B) := by
      rw [Set.uIcc_of_le hbB.le]
      exact hsmallEq
    exact intervalIntegral.integral_congr hEqU
  calc
    (∫ a : ℝ in b..(1 / 2 : ℝ), f a) =
        (∫ a : ℝ in b..B, f a) + ∫ a : ℝ in B..(1 / 2 : ℝ), f a := hsplit.symm
    _ = (∫ a : ℝ in b..B, g a) + ∫ a : ℝ in B..(1 / 2 : ℝ), f a := by rw [hsmallIntegral]

lemma prime_rough_of_gt {x b : ℝ} {n : ℕ} (hx : 1 < x) (hb : b < 1)
    (hn : Nat.Prime n) (hxn : x < (n : ℝ)) : rough (x ^ b) n := by
  refine ⟨hn.pos, ?_⟩
  intro q hq hqn
  have hqeq : n = q := (hn.dvd_iff_eq hq.ne_one).1 hqn
  have hpow : x ^ b < x := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hx hb
  rw [← hqeq]
  exact hpow.trans hxn

lemma prime_dyadic_subset_rough {x b : ℝ} (hx : 1 < x) (hb : b < 1) :
    (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime ⊆
      (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b)) := by
  intro n hn
  have hmem := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hmem.1, prime_rough_of_gt hx hb hmem.2 ?_⟩
  have hfloor : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem.1).1
  have hfloorCast : (⌊x⌋₊ : ℝ) < n := by exact_mod_cast hfloor
  have hnext : ⌊x⌋₊ + 1 ≤ n := Nat.succ_le_of_lt hfloor
  have hnextCast : (⌊x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hnext
  have hxFloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

theorem roughDyadicLower_base {b eps : ℝ} (hC : ClassicalInputs)
    (hbHalf : 1 / 2 ≤ b) (hbOne : b < 1) (heps : 0 < eps) (heps1 : eps < 1) :
    ∀ᶠ x : ℝ in atTop,
      roughDensity b 1 - eps ≤ L x / x *
        (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b))).card : ℝ) := by
  have hb : 0 < b := by linarith
  have hD : roughDensity b 1 = 1 := roughDensity_eq_one_of_ge_half hbHalf hbOne
  filter_upwards [prime_dyadic_count_lower hC heps heps1,
      eventually_gt_atTop (2 : ℝ)] with x hprime hx
  have hx1 : 1 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hrough := prime_dyadic_subset_rough hx1 hbOne
  have hcard :
      (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime).card : ℝ) ≤
        (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hrough
  have hfactor : 0 ≤ Real.log x / x := div_nonneg hlog.le (le_of_lt (by linarith : 0 < x))
  have hscaled : (1 - eps) ≤ Real.log x / x *
      (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hprime hfactor
    have hxpos : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
    have hlogne : Real.log x ≠ 0 := ne_of_gt hlog
    have hleft : (Real.log x / x) * ((1 - eps) * x / Real.log x) = 1 - eps := by
      field_simp [hxpos, hlogne] <;> ring
    rw [hleft] at hmul
    simpa [mul_comm] using hmul
  calc
    roughDensity b 1 - eps = 1 - eps := by rw [hD]
    _ ≤ Real.log x / x *
        (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime).card : ℝ) := hscaled
    _ ≤ Real.log x / x *
        (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b))).card : ℝ) :=
          mul_le_mul_of_nonneg_left hcard hfactor

lemma primeDyadicNormalizedLower {eps : ℝ} (hC : ClassicalInputs)
    (heps : 0 < eps) (heps1 : eps < 1) :
    ∀ᶠ x : ℝ in atTop,
      1 - eps ≤ L x / x *
        (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime).card : ℝ) := by
  filter_upwards [prime_dyadic_count_lower hC heps heps1,
      eventually_gt_atTop (2 : ℝ)] with x hprime hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hfactor : 0 ≤ Real.log x / x := div_nonneg hlog.le hxpos.le
  have hmul := mul_le_mul_of_nonneg_left hprime hfactor
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hlogne : Real.log x ≠ 0 := ne_of_gt hlog
  have hleft : (Real.log x / x) * ((1 - eps) * x / Real.log x) = 1 - eps := by
    field_simp [hxne, hlogne] <;> ring
  rw [hleft] at hmul
  simpa [Analytic.L, mul_comm] using hmul

lemma cofactor_threshold {x u : ℝ} {p : ℕ}
    (hx : 1 < x) (hu : 0 < u) (hu1 : u < 1) (hp : 0 < p)
    (hpu : (p : ℝ) ≤ x ^ u) :
    (p : ℝ) ≤ (x / p) ^ (u / (1 - u)) := by
  have hxpos : 0 < x := by linarith
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hpLog : Real.log (p : ℝ) ≤ u * Real.log x := by
    calc
      Real.log (p : ℝ) ≤ Real.log (x ^ u) := Real.log_le_log hpR hpu
      _ = u * Real.log x := by rw [Real.log_rpow hxpos]
  have hypos : 0 < x / (p : ℝ) := div_pos hxpos hpR
  have hlogy : (1 - u) * Real.log x ≤ Real.log (x / (p : ℝ)) := by
    rw [Real.log_div hxpos.ne' hpR.ne']
    linarith
  have hgamma : 0 < u / (1 - u) := div_pos hu (by linarith)
  have hlogpow : u * Real.log x ≤ (u / (1 - u)) * Real.log (x / (p : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hlogy hgamma.le
    have hcancel : (u / (1 - u)) * ((1 - u) * Real.log x) = u * Real.log x := by
      field_simp [ne_of_gt (by linarith : 0 < 1 - u)]
    rw [hcancel] at hmul
    exact hmul
  calc
    (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log hpR).symm
    _ ≤ Real.exp ((u / (1 - u)) * Real.log (x / (p : ℝ))) :=
      Real.exp_le_exp.mpr (hpLog.trans hlogpow)
    _ = (x / p) ^ (u / (1 - u)) := by
      rw [Real.rpow_def_of_pos hypos]
      ring

lemma rough_mul_of_rough_cofactor {x b : ℝ} {p m : ℕ} {gamma : ℝ}
    (hb : x ^ b < (p : ℝ)) (hp : Nat.Prime p)
    (hthreshold : (p : ℝ) ≤ (x / p) ^ gamma)
    (hm : rough ((x / p) ^ gamma) m) : rough (x ^ b) (p * m) := by
  refine ⟨Nat.mul_pos hp.pos hm.1, ?_⟩
  intro q hq hqdiv
  rcases (Nat.Prime.dvd_mul hq).mp hqdiv with hqp | hqm
  · have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    rw [hqeq]
    exact hb
  · exact lt_trans hb (lt_of_le_of_lt hthreshold (hm.2 q hq hqm))

lemma cofactor_pair_product_interval {x : ℝ} {p m : ℕ}
    (hx : 0 < x) (hp : 0 < p) (hmlo : ⌊x / p⌋₊ < m) (hmhi : m ≤ ⌊2 * x / p⌋₊) :
    ⌊x⌋₊ < p * m ∧ p * m ≤ ⌊2 * x⌋₊ := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hfloorx : x / (p : ℝ) < (⌊x / p⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (x / p)
  have hmlo' : (⌊x / p⌋₊ : ℝ) + 1 ≤ m := by
    exact_mod_cast Nat.succ_le_of_lt hmlo
  have hlow : x / p < m := lt_of_lt_of_le hfloorx hmlo'
  have hlowmul : x < (p : ℝ) * m := by
    have htmp : x < (m : ℝ) * p := (div_lt_iff₀ hpR).mp hlow
    nlinarith
  have hfloorX : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx.le
  have hupper' : (m : ℝ) ≤ 2 * x / p := by
    exact le_trans (by exact_mod_cast hmhi) (Nat.floor_le (by positivity))
  have huppermul : (p : ℝ) * m ≤ 2 * x := by
    have htmp := (le_div_iff₀ hpR).mp hupper'
    nlinarith
  constructor
  · exact_mod_cast (lt_of_le_of_lt hfloorX hlowmul)
  · have hprodCast : (↑(p * m) : ℝ) ≤ 2 * x := by
      simpa only [Nat.cast_mul] using huppermul
    exact Nat.le_floor hprodCast

def roughDyadicFinset (x b : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b))

def primeDyadicFinset (x : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime

def cofactorRoughFinset (x gamma : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Ioc ⌊x / p⌋₊ ⌊2 * x / p⌋₊).filter (rough ((x / p) ^ gamma))

def LowerCountStatement (b : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ᶠ x : ℝ in atTop,
    roughDensity b 1 - eps ≤ L x / x * (roughDyadicFinset x b).card

def DensityIntegralIdentity : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 →
    (∫ a : ℝ in b..(1 / 2 : ℝ), roughDensity a (1 - a) / a) =
      roughDensity b 1 - 1

def gridPoint (b step : ℝ) (i : ℕ) : ℝ := b + (i : ℝ) * step

def gridLowerCoeff (g : ℝ → ℝ) (b B : ℝ) (N i : ℕ) : ℝ :=
  g (gridPoint b ((B - b) / (N : ℝ)) (i + 1)) *
    (1 - gridPoint b ((B - b) / (N : ℝ)) (i + 1)) /
      (1 - gridPoint b ((B - b) / (N : ℝ)) i)

def gridGamma (b step : ℝ) (i : ℕ) : ℝ :=
  gridPoint b step (i + 1) / (1 - gridPoint b step (i + 1))

lemma gridPoint_zero (b step : ℝ) : gridPoint b step 0 = b := by simp [gridPoint]

lemma gridPoint_succ (b step : ℝ) (i : ℕ) :
    gridPoint b step (i + 1) - gridPoint b step i = step := by
  unfold gridPoint
  push_cast
  ring

lemma gridPoint_mono {b step : ℝ} (hstep : 0 ≤ step) {i j : ℕ} (hij : i ≤ j) :
    gridPoint b step i ≤ gridPoint b step j := by
  unfold gridPoint
  simpa [add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hstep) b

lemma gridPoint_mem_Icc {b B : ℝ} {N i : ℕ} (hbB : b ≤ B) (hN : 0 < N)
    (hi : i ≤ N) :
    gridPoint b ((B - b) / (N : ℝ)) i ∈ Set.Icc b B := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hstep : 0 ≤ (B - b) / (N : ℝ) := div_nonneg (sub_nonneg.mpr hbB) hNpos.le
  have hiR : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
  constructor
  · unfold gridPoint
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hstep)
  · have hmul := mul_le_mul_of_nonneg_right hiR hstep
    have hNmul : (N : ℝ) * ((B - b) / (N : ℝ)) = B - b := by
      field_simp [ne_of_gt hNpos]
    unfold gridPoint
    calc
      b + (i : ℝ) * ((B - b) / (N : ℝ)) ≤ b + (N : ℝ) * ((B - b) / (N : ℝ)) :=
        by simpa [add_comm] using add_le_add_left hmul b
      _ = B := by rw [hNmul]; ring

lemma intervalIntegral_inv_eq_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, t⁻¹) = Real.log b - Real.log a := by
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc a b) := by
    apply continuousOn_id.inv₀
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt Real.log t⁻¹ t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le ha ht.1))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

lemma gridLogTelescope (b step : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N,
      (Real.log (gridPoint b step (i + 1)) - Real.log (gridPoint b step i))) =
      Real.log (gridPoint b step N) - Real.log b := by
  induction N with
  | zero => simp [gridPoint_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

lemma exists_grid_lower_sum {b B eps : ℝ} (hb : 0 < b) (hbB : b < B)
    (hB : B < 1 / 2) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc b B))
    (hg0 : ∀ a ∈ Set.Icc b B, 0 ≤ g a) (heps : 0 < eps) :
    ∃ N : ℕ, 0 < N ∧
      (∫ t : ℝ in b..B, g t / t) - eps ≤
        ∑ i ∈ Finset.range N,
          gridLowerCoeff g b B N i *
            (Real.log (gridPoint b ((B - b) / (N : ℝ)) (i + 1)) -
              Real.log (gridPoint b ((B - b) / (N : ℝ)) i)) := by
  let K : Set ℝ := Set.Icc b B
  have hK : IsCompact K := isCompact_Icc
  have hUC : UniformContinuousOn g K := hK.uniformContinuousOn_of_continuous hg
  have hBdd : BddAbove (g '' K) := hK.bddAbove_image hg
  rcases hBdd with ⟨Mraw, hMraw⟩
  let M : ℝ := max 1 Mraw
  have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
  have hMbound : ∀ a ∈ K, g a ≤ M := by
    intro a ha
    have hmember : g a ∈ g '' K := ⟨a, ha, rfl⟩
    exact (hMraw hmember).trans (le_max_right _ _)
  let Q : ℝ := (B - b) / b
  let err : ℝ := eps / (2 * (Q + 1))
  have hQpos : 0 < Q := div_pos (sub_pos.mpr hbB) hb
  have herr : 0 < err := by dsimp [err]; positivity
  have herrorBudget : err * Q ≤ eps := by
    dsimp [err]
    field_simp [ne_of_gt (by positivity : 0 < 2 * (Q + 1))]
    nlinarith [heps, hQpos]
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) (err / 2) (by positivity)
  let mesh : ℝ := min δ (err / (4 * (M + 1)))
  have hmesh : 0 < mesh := by
    dsimp [mesh]
    apply lt_min hδ
    positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((B - b) / mesh)
  have hNpos : 0 < N := by
    by_contra hn
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos hn
    rw [hNzero] at hN
    have hratio : 0 < (B - b) / mesh := div_pos (sub_pos.mpr hbB) hmesh
    norm_num at hN
    linarith
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  let step : ℝ := (B - b) / (N : ℝ)
  have hstepNonneg : 0 ≤ step := by dsimp [step]; positivity
  have hstepLt : step < mesh := by
    have hmul : B - b < (N : ℝ) * mesh := (div_lt_iff₀ hmesh).1 hN
    dsimp [step]
    exact (div_lt_iff₀ hNposR).2 (by nlinarith [hmul])
  have hstepErr : step ≤ err / (4 * (M + 1)) := by
    exact (hstepLt.le.trans (min_le_right δ _))
  have hgridEnd : gridPoint b step N = B := by
    dsimp [gridPoint, step]
    field_simp [ne_of_gt hNposR]
    ring
  have hgridStart : gridPoint b step 0 = b := gridPoint_zero b step
  have hgridLog :
      (∑ i ∈ Finset.range N,
        (Real.log (gridPoint b step (i + 1)) - Real.log (gridPoint b step i))) =
        Real.log B - Real.log b := by
    calc
      _ = Real.log (gridPoint b step N) - Real.log b := gridLogTelescope b step N
      _ = Real.log B - Real.log b := by rw [hgridEnd]
  have hInvCont : ContinuousOn (fun t : ℝ => t⁻¹) K := by
    apply continuousOn_id.inv₀
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hb (Set.mem_Icc.mp ht).1)
  have hFCont : ContinuousOn (fun t : ℝ => g t / t) K := by
    apply hg.div continuousOn_id
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hb (Set.mem_Icc.mp ht).1)
  have hInvBound : (∫ t : ℝ in b..B, t⁻¹) ≤ Q := by
    have hconst : IntervalIntegrable (fun _ : ℝ => b⁻¹) volume b B :=
      continuousOn_const.intervalIntegrable_of_Icc hbB.le
    have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume b B :=
      hInvCont.intervalIntegrable_of_Icc hbB.le
    have hmono : (∫ t : ℝ in b..B, t⁻¹) ≤ ∫ t : ℝ in b..B, b⁻¹ := by
      apply intervalIntegral.integral_mono_on hbB.le hinv hconst
      intro t ht
      simpa [one_div] using one_div_le_one_div_of_le hb ht.1
    calc
      (∫ t : ℝ in b..B, t⁻¹) ≤ ∫ t : ℝ in b..B, b⁻¹ := hmono
      _ = Q := by simp [Q, smul_eq_mul, div_eq_mul_inv] <;> ring
  have hInvTotal : Real.log B - Real.log b ≤ Q := by
    rw [← intervalIntegral_inv_eq_log hb hbB.le]
    exact hInvBound
  have hErrTotal : err * (Real.log B - Real.log b) ≤ eps := by
    exact (mul_le_mul_of_nonneg_left hInvTotal herr.le).trans herrorBudget
  have hsumF :
      (∑ i ∈ Finset.range N,
        ∫ t : ℝ in gridPoint b step i..gridPoint b step (i + 1), g t / t) =
        ∫ t : ℝ in b..B, g t / t := by
    have hint : ∀ i < N,
        IntervalIntegrable (fun t : ℝ => g t / t) volume
          (gridPoint b step i) (gridPoint b step (i + 1)) := by
      intro i hi
      have hiK := gridPoint_mem_Icc (le_of_lt hbB) hNpos (Nat.le_of_lt hi)
      have hi1K := gridPoint_mem_Icc (le_of_lt hbB) hNpos (Nat.succ_le_of_lt hi)
      have hle : gridPoint b step i ≤ gridPoint b step (i + 1) :=
        gridPoint_mono hstepNonneg (Nat.le_succ i)
      have hsub : Set.Icc (gridPoint b step i) (gridPoint b step (i + 1)) ⊆ K :=
        Set.Icc_subset_Icc hiK.1 hi1K.2
      exact (hFCont.mono hsub).intervalIntegrable_of_Icc hle
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (μ := volume) (f := fun t : ℝ => g t / t)
      (a := fun i => gridPoint b step i) (n := N) hint
    simpa [hgridStart, hgridEnd] using hsum
  have hsumInv :
      (∑ i ∈ Finset.range N,
        ∫ t : ℝ in gridPoint b step i..gridPoint b step (i + 1), t⁻¹) =
        ∫ t : ℝ in b..B, t⁻¹ := by
    have hint : ∀ i < N,
        IntervalIntegrable (fun t : ℝ => t⁻¹) volume
          (gridPoint b step i) (gridPoint b step (i + 1)) := by
      intro i hi
      have hiK := gridPoint_mem_Icc (le_of_lt hbB) hNpos (Nat.le_of_lt hi)
      have hi1K := gridPoint_mem_Icc (le_of_lt hbB) hNpos (Nat.succ_le_of_lt hi)
      have hle : gridPoint b step i ≤ gridPoint b step (i + 1) :=
        gridPoint_mono hstepNonneg (Nat.le_succ i)
      have hsub : Set.Icc (gridPoint b step i) (gridPoint b step (i + 1)) ⊆ K :=
        Set.Icc_subset_Icc hiK.1 hi1K.2
      exact (hInvCont.mono hsub).intervalIntegrable_of_Icc hle
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (μ := volume) (f := fun t : ℝ => t⁻¹)
      (a := fun i => gridPoint b step i) (n := N) hint
    simpa [hgridStart, hgridEnd] using hsum
  have hbin : ∀ i ∈ Finset.range N,
      (∫ t : ℝ in gridPoint b step i..gridPoint b step (i + 1), g t / t) ≤
        (gridLowerCoeff g b B N i + err) *
          (Real.log (gridPoint b step (i + 1)) - Real.log (gridPoint b step i)) := by
    intro i hi
    have hiLt : i < N := Finset.mem_range.mp hi
    have aiK := gridPoint_mem_Icc (le_of_lt hbB) hNpos (Nat.le_of_lt hiLt)
    have uiK := gridPoint_mem_Icc (le_of_lt hbB) hNpos (Nat.succ_le_of_lt hiLt)
    let ai := gridPoint b step i
    let ui := gridPoint b step (i + 1)
    let ci := gridLowerCoeff g b B N i
    have hlen : ui - ai = step := by
      dsimp [ai, ui]
      exact gridPoint_succ b step i
    have hle : ai ≤ ui := by linarith [hlen, hstepNonneg]
    have hAiDen : 0 < 1 - ai := by linarith [aiK.2, hB]
    have hUiDen : 0 < 1 - ui := by linarith [uiK.2, hB]
    have hfracPos : 0 ≤ (ui - ai) / (1 - ai) := div_nonneg (sub_nonneg.mpr hle) hAiDen.le
    have hfrac : (ui - ai) / (1 - ai) ≤ 2 * step := by
      apply (div_le_iff₀ hAiDen).2
      have hhalf : 1 / 2 ≤ 1 - ai := by linarith [aiK.2, hB]
      rw [hlen]
      nlinarith [hhalf, hstepNonneg]
    have hci : ci = g ui * (1 - ui) / (1 - ai) := by
      dsimp [ci, gridLowerCoeff, ai, ui, step]
    have hcoefEq : g ui - ci = g ui * ((ui - ai) / (1 - ai)) := by
      rw [hci]
      field_simp [ne_of_gt hAiDen]
      <;> ring
    have hgu0 : 0 ≤ g ui := hg0 ui uiK
    have hguM : g ui ≤ M := hMbound ui uiK
    have hcoefGap : g ui - ci ≤ 2 * M * step := by
      rw [hcoefEq]
      calc
        g ui * ((ui - ai) / (1 - ai)) ≤ M * ((ui - ai) / (1 - ai)) :=
          mul_le_mul_of_nonneg_right hguM hfracPos
        _ ≤ M * (2 * step) := mul_le_mul_of_nonneg_left hfrac hMnonneg
        _ = 2 * M * step := by ring
    have hsmall : 2 * M * step ≤ err / 2 := by
      have hstepErr : step ≤ err / (4 * (M + 1)) :=
        hstepLt.le.trans (min_le_right δ _)
      have hstepProd : step * (4 * (M + 1)) ≤ err :=
        (le_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp hstepErr
      calc
        2 * M * step ≤ 2 * (M + 1) * step := by nlinarith [hMnonneg, hstepNonneg]
        _ = (step * (4 * (M + 1))) / 2 := by ring
        _ ≤ err / 2 := by linarith
    have hpoint : ∀ t ∈ Set.Icc ai ui, g t ≤ ci + err := by
      intro t ht
      have htK : t ∈ K := Set.Icc_subset_Icc aiK.1 uiK.2 ht
      have hdist : dist t ui < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
        have hlen' : ui - t ≤ step := by rw [← hlen]; linarith [ht.1]
        simpa [sub_eq_add_neg] using
          lt_of_le_of_lt hlen' (lt_of_lt_of_le hstepLt (min_le_left _ _))
      have hmod' := hmod t htK ui uiK hdist
      have hclose : g t < g ui + err / 2 := by
        have habs : |g t - g ui| < err / 2 := by
          simpa [Real.dist_eq, abs_sub_comm] using hmod'
        linarith [(abs_lt.mp habs).2]
      linarith [hcoefGap, hsmall]
    have hFint : IntervalIntegrable (fun t : ℝ => g t / t) volume ai ui := by
      have hsub : Set.Icc ai ui ⊆ K := Set.Icc_subset_Icc aiK.1 uiK.2
      exact (hFCont.mono hsub).intervalIntegrable_of_Icc hle
    have hstepCont : ContinuousOn (fun t : ℝ => (ci + err) / t) K := by
      apply continuousOn_const.div continuousOn_id
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le hb (Set.mem_Icc.mp ht).1)
    have hStepInt : IntervalIntegrable (fun t : ℝ => (ci + err) / t) volume ai ui := by
      have hsub : Set.Icc ai ui ⊆ K := Set.Icc_subset_Icc aiK.1 uiK.2
      exact (hstepCont.mono hsub).intervalIntegrable_of_Icc hle
    have hmono :
        (∫ t : ℝ in ai..ui, g t / t) ≤
          ∫ t : ℝ in ai..ui, (ci + err) / t := by
      apply intervalIntegral.integral_mono_on hle hFint hStepInt
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hb (Set.Icc_subset_Icc aiK.1 uiK.2 ht).1
      exact div_le_div_of_nonneg_right (hpoint t ht) htpos.le
    have hconstInt :
        (∫ t : ℝ in ai..ui, (ci + err) / t) =
          (ci + err) * (Real.log ui - Real.log ai) := by
      calc
        _ = (ci + err) * (∫ t : ℝ in ai..ui, t⁻¹) := by
          rw [show (fun t : ℝ => (ci + err) / t) = fun t => (ci + err) * t⁻¹ by
            funext t; ring]
          rw [intervalIntegral.integral_const_mul]
        _ = _ := by rw [intervalIntegral_inv_eq_log (lt_of_lt_of_le hb aiK.1) hle]
    simpa [ai, ui, ci] using hmono.trans_eq hconstInt
  have hsumBin :
      (∑ i ∈ Finset.range N,
        ∫ t : ℝ in gridPoint b step i..gridPoint b step (i + 1), g t / t) ≤
        ∑ i ∈ Finset.range N,
          (gridLowerCoeff g b B N i + err) *
            (Real.log (gridPoint b step (i + 1)) - Real.log (gridPoint b step i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hbin i hi
  have hsumExpand :
      (∑ i ∈ Finset.range N,
        (gridLowerCoeff g b B N i + err) *
          (Real.log (gridPoint b step (i + 1)) - Real.log (gridPoint b step i))) =
        (∑ i ∈ Finset.range N,
          gridLowerCoeff g b B N i *
            (Real.log (gridPoint b step (i + 1)) - Real.log (gridPoint b step i))) +
          err * (Real.log B - Real.log b) := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hgridLog]
  have hsumF := hsumF
  have hsumInv := hsumInv
  have hErrLog : err * (Real.log B - Real.log b) ≤ eps := hErrTotal
  refine ⟨N, hNpos, ?_⟩
  have hfull := hsumF.symm.trans_le hsumBin
  rw [hsumExpand] at hfull
  linarith

lemma gridLowerCoeff_density_eq {b step : ℝ} (N : ℕ) (hN : 0 < N) (i : ℕ)
    (hAi : gridPoint b step i < 1) (hUi : gridPoint b step (i + 1) < 1) :
    gridLowerCoeff leastFactorDensity b (gridPoint b step N) N i =
      roughDensity (gridGamma b step i) 1 / (1 - gridPoint b step i) := by
  have hstepEq : (gridPoint b step N - b) / (N : ℝ) = step := by
    unfold gridPoint
    field_simp [ne_of_gt (by exact_mod_cast hN : 0 < (N : ℝ))]
    ring
  unfold gridLowerCoeff
  rw [hstepEq]
  unfold leastFactorDensity gridGamma
  field_simp [ne_of_gt (sub_pos.mpr hAi), ne_of_gt (sub_pos.mpr hUi)]
  <;> ring

def cofactorPairFinset (x gamma : ℝ) (P : Finset ℕ) : Finset (Σ _p : ℕ, ℕ) :=
  P.sigma fun p =>
    (Finset.Ioc ⌊x / p⌋₊ ⌊2 * x / p⌋₊).filter (rough ((x / p) ^ gamma))

def primeExponentBin (x lo hi : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x ^ lo⌋₊ ⌊x ^ hi⌋₊).filter Nat.Prime

lemma primeExponentBin_bounds {x lo hi : ℝ} {p : ℕ}
    (hx : 0 ≤ x) (hp : p ∈ primeExponentBin x lo hi) :
    x ^ lo < (p : ℝ) ∧ (p : ℝ) ≤ x ^ hi := by
  have hmem := (Finset.mem_filter.mp hp).1
  constructor
  · have hnext : (⌊x ^ lo⌋₊ : ℝ) + 1 ≤ p := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_Ioc.mp hmem).1
    exact lt_of_lt_of_le (Nat.lt_floor_add_one (x ^ lo)) hnext
  · exact le_trans (by exact_mod_cast (Finset.mem_Ioc.mp hmem).2)
      (Nat.floor_le (Real.rpow_nonneg hx _))

lemma primeExponentBins_disjoint {x b step : ℝ} (hx : 1 < x) (hstep : 0 ≤ step)
    {N i j : ℕ} (hi : i ∈ Finset.range N) (hj : j ∈ Finset.range N)
    {p : ℕ} (hpi : p ∈ primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)))
    (hpj : p ∈ primeExponentBin x (gridPoint b step j) (gridPoint b step (j + 1))) : i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hgrid : gridPoint b step (i + 1) ≤ gridPoint b step j :=
      gridPoint_mono hstep (Nat.succ_le_of_lt hij')
    have hpi' := primeExponentBin_bounds (by linarith : 0 ≤ x) hpi
    have hpj' := primeExponentBin_bounds (by linarith : 0 ≤ x) hpj
    have hpow : x ^ gridPoint b step (i + 1) ≤ x ^ gridPoint b step j :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hgrid
    exact (not_lt_of_ge (hpi'.2.trans hpow)) hpj'.1
  · have hgrid : gridPoint b step (j + 1) ≤ gridPoint b step i :=
      gridPoint_mono hstep (Nat.succ_le_of_lt hji')
    have hpj' := primeExponentBin_bounds (by linarith : 0 ≤ x) hpj
    have hpi' := primeExponentBin_bounds (by linarith : 0 ≤ x) hpi
    have hpow : x ^ gridPoint b step (j + 1) ≤ x ^ gridPoint b step i :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hgrid
    exact (not_lt_of_ge (hpj'.2.trans hpow)) hpi'.1

def cofactorBinPairFinset (x b step : ℝ) (N : ℕ) (gammaOf : ℕ → ℝ) :
    Finset (Σ i : ℕ, Σ _p : ℕ, ℕ) :=
  (Finset.range N).sigma fun i =>
    cofactorPairFinset x (gammaOf i)
      (primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)))

lemma cofactorPairFinset_mapsTo {x b gamma : ℝ} (hx : 0 < x) (P : Finset ℕ)
    (hparams : ∀ p ∈ P, p.Prime ∧ x ^ b < (p : ℝ) ∧
      (p : ℝ) ≤ (x / p) ^ gamma) :
    Set.MapsTo (fun z : Σ _p : ℕ, ℕ => z.1 * z.2)
      (cofactorPairFinset x gamma P) (roughDyadicFinset x b) := by
  intro z hz
  rcases Finset.mem_sigma.mp hz with ⟨hp, hm⟩
  rcases Finset.mem_filter.mp hm with ⟨hmIoc, hmrough⟩
  have hpdata := hparams z.1 hp
  have hpair := cofactor_pair_product_interval hx hpdata.1.pos
    (Finset.mem_Ioc.mp hmIoc).1 (Finset.mem_Ioc.mp hmIoc).2
  have hrough := rough_mul_of_rough_cofactor hpdata.2.1 hpdata.1 hpdata.2.2 hmrough
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hpair, hrough⟩

lemma cofactorPairFinset_product_injective {x b gamma : ℝ} (P : Finset ℕ)
    (hparams : ∀ p ∈ P, p.Prime ∧ x ^ b < (p : ℝ) ∧
      (p : ℝ) ≤ (x / p) ^ gamma) :
    Set.InjOn (fun z : Σ _p : ℕ, ℕ => z.1 * z.2)
      (cofactorPairFinset x gamma P : Set (Σ _p : ℕ, ℕ)) := by
  intro z hz w hw hprod
  rcases z with ⟨p, m⟩
  rcases w with ⟨q, n⟩
  change (⟨p, m⟩ : Σ p : ℕ, ℕ) ∈
    P.sigma (fun p => (Finset.Ioc ⌊x / p⌋₊ ⌊2 * x / p⌋₊).filter
      (rough ((x / p) ^ gamma))) at hz
  change (⟨q, n⟩ : Σ p : ℕ, ℕ) ∈
    P.sigma (fun p => (Finset.Ioc ⌊x / p⌋₊ ⌊2 * x / p⌋₊).filter
      (rough ((x / p) ^ gamma))) at hw
  rw [Finset.mem_sigma] at hz hw
  rcases hz with ⟨hp, hm⟩
  rcases hw with ⟨hq, hn⟩
  have hpdata := hparams p hp
  have hqdata := hparams q hq
  have hprod' : p * m = q * n := by simpa using hprod
  simp only [Sigma.mk.injEq]
  have hprough : ∀ r : ℕ, r.Prime → r ∣ m → (p : ℝ) < r := by
    intro r hr hrd
    have hmr := (Finset.mem_filter.mp hm).2
    exact lt_of_le_of_lt hpdata.2.2 (hmr.2 r hr hrd)
  have hqrough : ∀ r : ℕ, r.Prime → r ∣ n → (q : ℝ) < r := by
    intro r hr hrd
    have hnr := (Finset.mem_filter.mp hn).2
    exact lt_of_le_of_lt hqdata.2.2 (hnr.2 r hr hrd)
  have hpq : p = q := by
    by_contra hne
    have hdivP : p ∣ q * n := by
      have h : p ∣ p * m := ⟨m, rfl⟩
      rw [hprod'] at h
      exact h
    rcases (Nat.Prime.dvd_mul hpdata.1).mp hdivP with hpq' | hpn
    · exact hne ((Nat.prime_dvd_prime_iff_eq hpdata.1 hqdata.1).mp hpq')
    · have hqp : (q : ℝ) < p := hqrough p hpdata.1 hpn
      have hdivQ : q ∣ p * m := by
        have h : q ∣ q * n := ⟨n, rfl⟩
        rw [← hprod'] at h
        exact h
      rcases (Nat.Prime.dvd_mul hqdata.1).mp hdivQ with hqp' | hqm
      · exact hne ((Nat.prime_dvd_prime_iff_eq hqdata.1 hpdata.1).mp hqp').symm
      · have hpq' : (p : ℝ) < q := hprough q hqdata.1 hqm
        exact (not_lt_of_ge (le_of_lt hpq')) hqp
  refine ⟨hpq, ?_⟩
  subst q
  exact heq_of_eq (Nat.mul_left_cancel hpdata.1.pos hprod')

lemma cofactorPairFinset_card_le {x b gamma : ℝ} (hx : 0 < x) (P : Finset ℕ)
    (hparams : ∀ p ∈ P, p.Prime ∧ x ^ b < (p : ℝ) ∧
      (p : ℝ) ≤ (x / p) ^ gamma) :
    (cofactorPairFinset x gamma P).card ≤ (roughDyadicFinset x b).card :=
  Finset.card_le_card_of_injOn (fun z : Σ _p : ℕ, ℕ => z.1 * z.2)
    (cofactorPairFinset_mapsTo hx P hparams)
    (cofactorPairFinset_product_injective P hparams)

lemma cofactorPairFinset_card_eq {x gamma : ℝ} (P : Finset ℕ) :
    (cofactorPairFinset x gamma P).card =
      ∑ p ∈ P,
        ((Finset.Ioc ⌊x / p⌋₊ ⌊2 * x / p⌋₊).filter
          (rough ((x / p) ^ gamma))).card := by
  simp [cofactorPairFinset, Finset.card_sigma]

lemma cofactorBinPairFinset_card_eq (x b step : ℝ) (N : ℕ) (gammaOf : ℕ → ℝ) :
    (cofactorBinPairFinset x b step N gammaOf).card =
      ∑ i ∈ Finset.range N, ∑ p ∈ primeExponentBin x
          (gridPoint b step i) (gridPoint b step (i + 1)),
        (cofactorRoughFinset x (gammaOf i) p).card := by
  simp [cofactorBinPairFinset, cofactorPairFinset, cofactorRoughFinset,
    Finset.card_sigma, primeExponentBin]

lemma cofactorBinPairFinset_mapsTo {x b step : ℝ} (hx : 0 < x) (N : ℕ)
    (gammaOf : ℕ → ℝ)
    (hparams : ∀ i ∈ Finset.range N, ∀ p ∈
      primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)),
        p.Prime ∧ x ^ b < (p : ℝ) ∧ (p : ℝ) ≤ (x / p) ^ (gammaOf i)) :
    Set.MapsTo (fun z : Σ i : ℕ, Σ _p : ℕ, ℕ => z.2.1 * z.2.2)
      (cofactorBinPairFinset x b step N gammaOf) (roughDyadicFinset x b) := by
  intro z hz
  rcases z with ⟨i, pair⟩
  change ⟨i, pair⟩ ∈ (Finset.range N).sigma (fun i =>
    cofactorPairFinset x (gammaOf i)
      (primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)))) at hz
  rw [Finset.mem_sigma] at hz
  rcases hz with ⟨hi, hpairs⟩
  exact cofactorPairFinset_mapsTo hx _ (hparams i hi) hpairs

lemma cofactorBinPairFinset_product_injective {x b step : ℝ} (N : ℕ)
    (gammaOf : ℕ → ℝ)
    (hparams : ∀ i ∈ Finset.range N, ∀ p ∈
      primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)),
        p.Prime ∧ x ^ b < (p : ℝ) ∧ (p : ℝ) ≤ (x / p) ^ (gammaOf i))
    (hbin : ∀ i j p, i ∈ Finset.range N → j ∈ Finset.range N →
      p ∈ primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)) →
      p ∈ primeExponentBin x (gridPoint b step j) (gridPoint b step (j + 1)) → i = j) :
    Set.InjOn (fun z : Σ i : ℕ, Σ _p : ℕ, ℕ => z.2.1 * z.2.2)
      (cofactorBinPairFinset x b step N gammaOf : Set (Σ i : ℕ, Σ _p : ℕ, ℕ)) := by
  intro z hz w hw hprod
  rcases z with ⟨i, ⟨p, m⟩⟩
  rcases w with ⟨j, ⟨q, n⟩⟩
  change ⟨i, ⟨p, m⟩⟩ ∈ (Finset.range N).sigma (fun i =>
    cofactorPairFinset x (gammaOf i)
      (primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)))) at hz
  change ⟨j, ⟨q, n⟩⟩ ∈ (Finset.range N).sigma (fun i =>
    cofactorPairFinset x (gammaOf i)
      (primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)))) at hw
  rw [Finset.mem_sigma] at hz hw
  rcases hz with ⟨hi, hpair⟩
  rcases hw with ⟨hj, hpair'⟩
  have hPi : p ∈ primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)) :=
    (Finset.mem_sigma.mp hpair).1
  have hQi : q ∈ primeExponentBin x (gridPoint b step j) (gridPoint b step (j + 1)) :=
    (Finset.mem_sigma.mp hpair').1
  have hm : m ∈ cofactorRoughFinset x (gammaOf i) p :=
    (Finset.mem_sigma.mp hpair).2
  have hn : n ∈ cofactorRoughFinset x (gammaOf j) q :=
    (Finset.mem_sigma.mp hpair').2
  have hpdata := hparams i hi p hPi
  have hqdata := hparams j hj q hQi
  have hprod' : p * m = q * n := by simpa using hprod
  have hprough : ∀ r : ℕ, r.Prime → r ∣ m → (p : ℝ) < r := by
    intro r hr hrd
    exact lt_of_le_of_lt hpdata.2.2 ((Finset.mem_filter.mp hm).2.2 r hr hrd)
  have hqrough : ∀ r : ℕ, r.Prime → r ∣ n → (q : ℝ) < r := by
    intro r hr hrd
    exact lt_of_le_of_lt hqdata.2.2 ((Finset.mem_filter.mp hn).2.2 r hr hrd)
  have hpq : p = q := by
    by_contra hne
    have hdivP : p ∣ q * n := by
      have h : p ∣ p * m := ⟨m, rfl⟩
      rw [hprod'] at h
      exact h
    rcases (Nat.Prime.dvd_mul hpdata.1).mp hdivP with hpq' | hpn
    · exact hne ((Nat.prime_dvd_prime_iff_eq hpdata.1 hqdata.1).mp hpq')
    · have hqp : (q : ℝ) < p := hqrough p hpdata.1 hpn
      have hdivQ : q ∣ p * m := by
        have h : q ∣ q * n := ⟨n, rfl⟩
        rw [← hprod'] at h
        exact h
      rcases (Nat.Prime.dvd_mul hqdata.1).mp hdivQ with hqp' | hqm
      · exact hne ((Nat.prime_dvd_prime_iff_eq hqdata.1 hpdata.1).mp hqp').symm
      · have hpq' : (p : ℝ) < q := hprough q hqdata.1 hqm
        exact (not_lt_of_ge (le_of_lt hpq')) hqp
  have hij : i = j := hbin i j p hi hj hPi (by simpa [hpq] using hQi)
  subst j
  subst q
  have hmn : m = n := Nat.mul_left_cancel hpdata.1.pos hprod'
  subst n
  rfl

lemma cofactorBinPairFinset_card_le {x b step : ℝ} (hx : 0 < x) (N : ℕ)
    (gammaOf : ℕ → ℝ)
    (hparams : ∀ i ∈ Finset.range N, ∀ p ∈
      primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)),
        p.Prime ∧ x ^ b < (p : ℝ) ∧ (p : ℝ) ≤ (x / p) ^ (gammaOf i))
    (hbin : ∀ i j p, i ∈ Finset.range N → j ∈ Finset.range N →
      p ∈ primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)) →
      p ∈ primeExponentBin x (gridPoint b step j) (gridPoint b step (j + 1)) → i = j) :
    (cofactorBinPairFinset x b step N gammaOf).card ≤ (roughDyadicFinset x b).card :=
  Finset.card_le_card_of_injOn (fun z : Σ i : ℕ, Σ _p : ℕ, ℕ => z.2.1 * z.2.2)
    (cofactorBinPairFinset_mapsTo hx N gammaOf hparams)
    (cofactorBinPairFinset_product_injective N gammaOf hparams hbin)

lemma cofactor_count_lower_bin {a u gamma delta : ℝ}
    (hIH : LowerCountStatement gamma) (ha : 0 < a) (hu0 : 0 < u)
    (hau : a ≤ u) (hu1 : u < 1) (hgamma : gamma = u / (1 - u))
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ u⌋₊).filter Nat.Prime,
      (roughDensity gamma 1 - delta) * x /
        ((p : ℝ) * (1 - a) * L x) ≤ (cofactorRoughFinset x gamma p).card := by
  have hIHevent := hIH delta hdelta
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hIHevent
  have hpowEvent : ∀ᶠ x : ℝ in atTop, max 2 Y₀ ≤ x ^ (1 - u) := by
    have ht := tendsto_rpow_atTop (by linarith : 0 < 1 - u)
    exact ht.eventually (eventually_ge_atTop (max 2 Y₀))
  filter_upwards [hpowEvent, eventually_gt_atTop (2 : ℝ)] with x hxpow hx
  intro p hp
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := Real.log_pos hx1
  have hpIoc := Finset.mem_filter.mp hp |>.1
  have hpPrime := Finset.mem_filter.mp hp |>.2
  have hfloorLow : ⌊x ^ a⌋₊ < p := (Finset.mem_Ioc.mp hpIoc).1
  have hfloorLow' : (⌊x ^ a⌋₊ : ℝ) < p := by exact_mod_cast hfloorLow
  have hlow : x ^ a < (p : ℝ) := by
    have hnext : (⌊x ^ a⌋₊ : ℝ) + 1 ≤ p := by
      exact_mod_cast Nat.succ_le_of_lt hfloorLow
    have hxfloor : x ^ a < (⌊x ^ a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (x ^ a)
    exact lt_of_lt_of_le hxfloor hnext
  have hfloorHigh : p ≤ ⌊x ^ u⌋₊ := (Finset.mem_Ioc.mp hpIoc).2
  have hupper : (p : ℝ) ≤ x ^ u := by
    exact le_trans (by exact_mod_cast hfloorHigh) (Nat.floor_le (by positivity))
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  let y : ℝ := x / p
  have hylo : x ^ (1 - u) ≤ y := by
    have hrecip := one_div_le_one_div_of_le hpR hupper
    have hmul := mul_le_mul_of_nonneg_left hrecip hxpos.le
    have hscale : x / (x ^ u) = x ^ (1 - u) := by
      rw [Real.rpow_sub hxpos 1 u, Real.rpow_one]
    have hratio : x / (x ^ u) ≤ x / p := by
      simpa [div_eq_mul_inv] using hmul
    calc
      x ^ (1 - u) = x / (x ^ u) := hscale.symm
      _ ≤ x / p := hratio
      _ = y := rfl
  have hyge : Y₀ ≤ y := by
    have : max 2 Y₀ ≤ y := le_trans hxpow hylo
    exact (le_max_right _ _).trans this
  have hy2 : 2 ≤ y := le_trans (le_max_left _ _) (le_trans hxpow hylo)
  have hypos : 0 < y := by linarith
  have hlogypos : 0 < Real.log y := Real.log_pos (by linarith [hy2])
  have hlogx : Real.log x = L x := rfl
  have hlogp : a * L x < Real.log (p : ℝ) := by
    have hlogpow : Real.log (x ^ a) = a * L x := by
      rw [Real.log_rpow hxpos, hlogx]
    calc
      a * L x = Real.log (x ^ a) := hlogpow.symm
      _ < Real.log (p : ℝ) := Real.log_lt_log (Real.rpow_pos_of_pos hxpos a) hlow
  have hlogy : Real.log y = L x - Real.log (p : ℝ) := by
    dsimp [y]
    rw [Real.log_div hxpos.ne' hpR.ne', hlogx]
  have hlogyUpper : Real.log y ≤ (1 - a) * L x := by rw [hlogy]; linarith
  have hDpos : 0 ≤ roughDensity gamma 1 - delta := by
    have hgammaPos : 0 < gamma := by rw [hgamma]; positivity
    have hD := roughDensity_one_ge_one hgammaPos
    linarith
  have hthreshold : (p : ℝ) ≤ y ^ gamma := by
    dsimp [y]
    rw [hgamma]
    exact cofactor_threshold hx1 hu0 hu1 hpPrime.pos hupper
  have hIHy := hY₀ y hyge
  have hcof : roughDyadicFinset y gamma = cofactorRoughFinset x gamma p := by
    ext m
    simp only [roughDyadicFinset, cofactorRoughFinset, Finset.mem_filter, Finset.mem_Ioc]
    dsimp [y]
    have hupper' : 2 * (x / (p : ℝ)) = 2 * x / p := by
      field_simp [ne_of_gt hpR] <;> ring
    rw [hupper']
  have hcountScaled : roughDensity gamma 1 - delta ≤
      Real.log y / y * (cofactorRoughFinset x gamma p).card := by
    rw [hcof] at hIHy
    simpa [Analytic.L] using hIHy
  have hyFactor : 0 < y / Real.log y := div_pos hypos hlogypos
  have hcount :
      (roughDensity gamma 1 - delta) * (y / Real.log y) ≤
        (cofactorRoughFinset x gamma p).card := by
    have hmul := mul_le_mul_of_nonneg_left hcountScaled hyFactor.le
    have hcancel : (y / Real.log y) * (Real.log y / y) = 1 := by
      field_simp [ne_of_gt hypos, ne_of_gt hlogypos]
    calc
      (roughDensity gamma 1 - delta) * (y / Real.log y) =
          (y / Real.log y) * (roughDensity gamma 1 - delta) := by ring
      _ ≤ (y / Real.log y) * (Real.log y / y *
          (cofactorRoughFinset x gamma p).card) := hmul
      _ = (cofactorRoughFinset x gamma p).card := by
        calc
          _ = ((y / Real.log y) * (Real.log y / y)) *
              (cofactorRoughFinset x gamma p).card := by ring
          _ = (cofactorRoughFinset x gamma p).card := by rw [hcancel, one_mul]
  have hdenPos : 0 < (1 - a) * L x := mul_pos (by linarith [hau, hu1]) hLpos
  have hrecip : ((1 - a) * L x)⁻¹ ≤ (Real.log y)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlogypos hlogyUpper
  have hydiv : y / ((1 - a) * L x) ≤ y / Real.log y := by
    calc
      y / ((1 - a) * L x) = y * ((1 - a) * L x)⁻¹ := by ring
      _ ≤ y * (Real.log y)⁻¹ := mul_le_mul_of_nonneg_left hrecip hypos.le
      _ = y / Real.log y := by ring
  have hscale : (roughDensity gamma 1 - delta) * x /
        ((p : ℝ) * (1 - a) * L x) =
      (roughDensity gamma 1 - delta) * (y / ((1 - a) * L x)) := by
    dsimp [y]
    field_simp [ne_of_gt hpR, ne_of_gt hdenPos]
    <;> ring
  calc
    (roughDensity gamma 1 - delta) * x /
        ((p : ℝ) * (1 - a) * L x) =
      (roughDensity gamma 1 - delta) * (y / ((1 - a) * L x)) := hscale
    _ ≤ (roughDensity gamma 1 - delta) * (y / Real.log y) :=
      mul_le_mul_of_nonneg_left hydiv hDpos
    _ ≤ (cofactorRoughFinset x gamma p).card := hcount

lemma roughDyadic_lower_from_bin {b a u gamma delta : ℝ}
    (hIH : LowerCountStatement gamma) (hb : 0 < b) (hba : b ≤ a)
    (ha : 0 < a) (hau : a ≤ u) (hu0 : 0 < u) (hu1 : u < 1)
    (hgamma : gamma = u / (1 - u)) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∀ᶠ x : ℝ in atTop,
      (roughDensity gamma 1 - delta) * x / ((1 - a) * L x) *
        scaledPrimeReciprocalInterval x a u ≤
          (roughDyadicFinset x b).card := by
  have hcof := cofactor_count_lower_bin hIH ha hu0 hau hu1 hgamma hdelta hdelta1
  filter_upwards [hcof, eventually_gt_atTop (2 : ℝ)] with x hcofX hx
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := Real.log_pos hx1
  let P : Finset ℕ := (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ u⌋₊).filter Nat.Prime
  have hparams : ∀ p ∈ P, p.Prime ∧ x ^ b < (p : ℝ) ∧ (p : ℝ) ≤ (x / p) ^ gamma := by
    intro p hp
    have hpIoc := (Finset.mem_filter.mp hp).1
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hloNat := (Finset.mem_Ioc.mp hpIoc).1
    have hlo : x ^ a < (p : ℝ) := by
      have hnext : (⌊x ^ a⌋₊ : ℝ) + 1 ≤ p := by
        exact_mod_cast Nat.succ_le_of_lt hloNat
      exact lt_of_lt_of_le (Nat.lt_floor_add_one (x ^ a)) hnext
    have hlowPow : x ^ b ≤ x ^ a :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hba
    have hupNat := (Finset.mem_Ioc.mp hpIoc).2
    have hup : (p : ℝ) ≤ x ^ u :=
      le_trans (by exact_mod_cast hupNat) (Nat.floor_le (by positivity))
    have hthreshold := cofactor_threshold hx1 hu0 hu1 hpPrime.pos hup
    have hthreshold' : (p : ℝ) ≤ (x / p) ^ gamma := by
      rw [hgamma]
      exact hthreshold
    exact ⟨hpPrime, lt_of_le_of_lt hlowPow hlo, hthreshold'⟩
  have hpairle : (cofactorPairFinset x gamma P).card ≤
      (roughDyadicFinset x b).card := cofactorPairFinset_card_le hxpos P hparams
  have hpairEq : (cofactorPairFinset x gamma P).card =
      ∑ p ∈ P, (cofactorRoughFinset x gamma p).card := by
    simpa [cofactorRoughFinset] using cofactorPairFinset_card_eq P
  have hsumCards :
      (∑ p ∈ P, (cofactorRoughFinset x gamma p).card : ℝ) =
        (cofactorPairFinset x gamma P).card := by
    exact_mod_cast hpairEq.symm
  have hsumLower :
      ∑ p ∈ P, (roughDensity gamma 1 - delta) * x /
          ((p : ℝ) * (1 - a) * L x) ≤
        ∑ p ∈ P, ((cofactorRoughFinset x gamma p).card : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hcofX p hp
  have hsumFactor :
      (∑ p ∈ P, (roughDensity gamma 1 - delta) * x /
          ((p : ℝ) * (1 - a) * L x)) =
        (roughDensity gamma 1 - delta) * x / ((1 - a) * L x) *
          scaledPrimeReciprocalInterval x a u := by
    unfold scaledPrimeReciprocalInterval
    rw [show P = (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ u⌋₊).filter Nat.Prime by rfl]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpdata := hparams p hp
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hpdata.1.pos
    field_simp [ne_of_gt hpR, ne_of_gt hLpos, ne_of_gt (by linarith [ha, hau, hu1] : 0 < 1 - a)]
    <;> ring
  have hcardReal :
      ((cofactorPairFinset x gamma P).card : ℝ) ≤
        ((roughDyadicFinset x b).card : ℝ) := by exact_mod_cast hpairle
  calc
    (roughDensity gamma 1 - delta) * x / ((1 - a) * L x) *
        scaledPrimeReciprocalInterval x a u =
      ∑ p ∈ P, (roughDensity gamma 1 - delta) * x /
        ((p : ℝ) * (1 - a) * L x) := hsumFactor.symm
    _ ≤ ∑ p ∈ P, ((cofactorRoughFinset x gamma p).card : ℝ) := hsumLower
    _ = (cofactorPairFinset x gamma P).card := hsumCards
    _ ≤ (roughDyadicFinset x b).card := hcardReal

lemma cofactorPair_lower_from_bin {a u gamma delta : ℝ}
    (hIH : LowerCountStatement gamma) (ha : 0 < a) (hu0 : 0 < u)
    (hau : a ≤ u) (hu1 : u < 1) (hgamma : gamma = u / (1 - u))
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∀ᶠ x : ℝ in atTop,
      (roughDensity gamma 1 - delta) * x / ((1 - a) * L x) *
        scaledPrimeReciprocalInterval x a u ≤
          (cofactorPairFinset x gamma
            ((Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ u⌋₊).filter Nat.Prime)).card := by
  have hcof := cofactor_count_lower_bin hIH ha hu0 hau hu1 hgamma hdelta hdelta1
  filter_upwards [hcof, eventually_gt_atTop (2 : ℝ)] with x hcofX hx
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := Real.log_pos hx1
  let P : Finset ℕ := (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ u⌋₊).filter Nat.Prime
  have hsumCards :
      (∑ p ∈ P, ((cofactorRoughFinset x gamma p).card : ℝ)) =
        (cofactorPairFinset x gamma P).card := by
    exact_mod_cast (cofactorPairFinset_card_eq P).symm
  have hsumLower :
      ∑ p ∈ P, (roughDensity gamma 1 - delta) * x /
          ((p : ℝ) * (1 - a) * L x) ≤
        ∑ p ∈ P, ((cofactorRoughFinset x gamma p).card : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hcofX p hp
  have hsumFactor :
      (∑ p ∈ P, (roughDensity gamma 1 - delta) * x /
          ((p : ℝ) * (1 - a) * L x)) =
        (roughDensity gamma 1 - delta) * x / ((1 - a) * L x) *
          scaledPrimeReciprocalInterval x a u := by
    unfold scaledPrimeReciprocalInterval
    rw [show P = (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ u⌋₊).filter Nat.Prime by rfl]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    field_simp [ne_of_gt hpR, ne_of_gt hLpos,
      ne_of_gt (by linarith [ha, hau, hu1] : 0 < 1 - a)]
    <;> ring
  calc
    (roughDensity gamma 1 - delta) * x / ((1 - a) * L x) *
        scaledPrimeReciprocalInterval x a u =
      ∑ p ∈ P, (roughDensity gamma 1 - delta) * x /
        ((p : ℝ) * (1 - a) * L x) := hsumFactor.symm
    _ ≤ ∑ p ∈ P, ((cofactorRoughFinset x gamma p).card : ℝ) := hsumLower
    _ = (cofactorPairFinset x gamma P).card := hsumCards

lemma cofactorBins_lower {b step delta : ℝ} (N : ℕ) (hN : 0 < N)
    (hb : 0 < b) (hstep : 0 < step) (hEnd : gridPoint b step N < 1 / 2)
    (hIH : ∀ i ∈ Finset.range N, LowerCountStatement (gridGamma b step i))
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∀ᶠ x : ℝ in atTop,
      (∑ i ∈ Finset.range N,
        (roughDensity (gridGamma b step i) 1 - delta) * x /
          ((1 - gridPoint b step i) * L x) *
            scaledPrimeReciprocalInterval x (gridPoint b step i)
              (gridPoint b step (i + 1))) ≤
        (cofactorBinPairFinset x b step N (gridGamma b step)).card := by
  have hEach : ∀ᶠ x : ℝ in atTop, ∀ i : Fin N,
      (roughDensity (gridGamma b step i.val) 1 - delta) * x /
        ((1 - gridPoint b step i.val) * L x) *
          scaledPrimeReciprocalInterval x (gridPoint b step i.val)
            (gridPoint b step (i.val + 1)) ≤
        (cofactorPairFinset x (gridGamma b step i.val)
          (primeExponentBin x (gridPoint b step i.val) (gridPoint b step (i.val + 1)))).card := by
    apply eventually_all.2
    intro i
    let k : ℕ := i.val
    have hk : k ∈ Finset.range N := Finset.mem_range.mpr i.isLt
    let a : ℝ := gridPoint b step k
    let u : ℝ := gridPoint b step (k + 1)
    have haLower : b ≤ a := by
      change b ≤ gridPoint b step k
      calc
        b = gridPoint b step 0 := (gridPoint_zero b step).symm
        _ ≤ gridPoint b step k := gridPoint_mono hstep.le (Nat.zero_le k)
    have huLower : b ≤ u := by
      change b ≤ gridPoint b step (k + 1)
      calc
        b = gridPoint b step 0 := (gridPoint_zero b step).symm
        _ ≤ gridPoint b step (k + 1) := gridPoint_mono hstep.le (Nat.zero_le (k + 1))
    have huEnd : u ≤ gridPoint b step N := by
      change gridPoint b step (k + 1) ≤ gridPoint b step N
      exact gridPoint_mono hstep.le (Nat.succ_le_of_lt i.isLt)
    have ha : 0 < a := lt_of_lt_of_le hb haLower
    have hu0 : 0 < u := lt_of_lt_of_le hb huLower
    have hau : a ≤ u := by
      dsimp [a, u]
      exact gridPoint_mono hstep.le (Nat.le_succ k)
    have hu1 : u < 1 := lt_of_le_of_lt huEnd (by linarith [hEnd])
    have hgamma : gridGamma b step k = u / (1 - u) := by rfl
    have hbin := cofactorPair_lower_from_bin (hIH k hk) ha hu0 hau hu1 hgamma hdelta hdelta1
    simpa [a, u, k, primeExponentBin] using hbin
  obtain ⟨x₀, hEachX⟩ := Filter.eventually_atTop.1 hEach
  filter_upwards [eventually_ge_atTop x₀] with x hx
  have hpairCard :
      ((cofactorBinPairFinset x b step N (gridGamma b step)).card : ℝ) =
        ∑ i ∈ Finset.range N, ∑ p ∈ primeExponentBin x
          (gridPoint b step i) (gridPoint b step (i + 1)),
          ((cofactorRoughFinset x (gridGamma b step i) p).card : ℝ) := by
    exact_mod_cast (cofactorBinPairFinset_card_eq x b step N (gridGamma b step))
  have hsumLower :
      (∑ i ∈ Finset.range N,
        (roughDensity (gridGamma b step i) 1 - delta) * x /
          ((1 - gridPoint b step i) * L x) *
            scaledPrimeReciprocalInterval x (gridPoint b step i)
              (gridPoint b step (i + 1))) ≤
        ∑ i ∈ Finset.range N, ∑ p ∈ primeExponentBin x
          (gridPoint b step i) (gridPoint b step (i + 1)),
          ((cofactorRoughFinset x (gridGamma b step i) p).card : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    let fi : Fin N := ⟨i, Finset.mem_range.mp hi⟩
    have h := hEachX x hx fi
    have hinner :
        ((cofactorPairFinset x (gridGamma b step i)
          (primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)))).card : ℝ) =
          ∑ p ∈ primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)),
            ((cofactorRoughFinset x (gridGamma b step i) p).card : ℝ) := by
      exact_mod_cast (cofactorPairFinset_card_eq _)
    rw [hinner] at h
    simpa using h
  calc
    (∑ i ∈ Finset.range N,
        (roughDensity (gridGamma b step i) 1 - delta) * x /
          ((1 - gridPoint b step i) * L x) *
            scaledPrimeReciprocalInterval x (gridPoint b step i)
              (gridPoint b step (i + 1))) ≤
      ∑ i ∈ Finset.range N, ∑ p ∈ primeExponentBin x
        (gridPoint b step i) (gridPoint b step (i + 1)),
        ((cofactorRoughFinset x (gridGamma b step i) p).card : ℝ) := hsumLower
    _ = (cofactorBinPairFinset x b step N (gridGamma b step)).card := hpairCard.symm

lemma cofactorBins_card_le_rough {x b step : ℝ} (N : ℕ) (hx : 1 < x)
    (hb : 0 < b) (hstep : 0 ≤ step) (hN : 0 < N)
    (hEnd : gridPoint b step N < 1 / 2) :
    (cofactorBinPairFinset x b step N (gridGamma b step)).card ≤
      (roughDyadicFinset x b).card := by
  have hxpos : 0 < x := by linarith
  have hEndLower : b ≤ gridPoint b step N := by
    unfold gridPoint
    exact le_add_of_nonneg_right (mul_nonneg (by positivity : 0 ≤ (N : ℝ)) hstep)
  have hparams : ∀ i ∈ Finset.range N, ∀ p ∈
      primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)),
      p.Prime ∧ x ^ b < (p : ℝ) ∧ (p : ℝ) ≤ (x / p) ^ (gridGamma b step i) := by
    intro i hi p hp
    have hpdata := primeExponentBin_bounds hxpos.le hp
    have hiLower : b ≤ gridPoint b step i := by
      calc
        b = gridPoint b step 0 := (gridPoint_zero b step).symm
        _ ≤ gridPoint b step i := gridPoint_mono hstep (Nat.zero_le i)
    have hiUpper : gridPoint b step i ≤ gridPoint b step N :=
      gridPoint_mono hstep (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hi1Lower : b ≤ gridPoint b step (i + 1) := by
      calc
        b = gridPoint b step 0 := (gridPoint_zero b step).symm
        _ ≤ gridPoint b step (i + 1) := gridPoint_mono hstep (Nat.zero_le (i + 1))
    have hi1Upper : gridPoint b step (i + 1) ≤ gridPoint b step N :=
      gridPoint_mono hstep (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    have hpow : x ^ b ≤ x ^ (gridPoint b step i) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hiLower
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have huPos : 0 < gridPoint b step (i + 1) := lt_of_lt_of_le hb hi1Lower
    have huLt : gridPoint b step (i + 1) < 1 :=
      lt_of_le_of_lt hi1Upper (by linarith [hEnd])
    have hthreshold := cofactor_threshold hx huPos huLt hpPrime.pos hpdata.2
    have hthreshold' : (p : ℝ) ≤ (x / p) ^ (gridGamma b step i) := by
      dsimp [gridGamma]
      exact hthreshold
    exact ⟨hpPrime, lt_of_le_of_lt hpow hpdata.1, hthreshold'⟩
  have hbin : ∀ i j p, i ∈ Finset.range N → j ∈ Finset.range N →
      p ∈ primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)) →
      p ∈ primeExponentBin x (gridPoint b step j) (gridPoint b step (j + 1)) → i = j := by
    intro i j p hi hj hpi hpj
    exact primeExponentBins_disjoint hx hstep hi hj hpi hpj
  exact cofactorBinPairFinset_card_le hxpos N (gridGamma b step) hparams hbin

lemma prime_and_pair_count_le_rough {x b step : ℝ} (N : ℕ) (hx : 2 < x)
    (hb : b < 1) (hstep : 0 ≤ step) (hN : 0 < N)
    (hEnd : gridPoint b step N < 1 / 2)
    (hparams : ∀ i ∈ Finset.range N, ∀ p ∈
      primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)),
        p.Prime ∧ x ^ b < (p : ℝ) ∧ (p : ℝ) ≤ (x / p) ^ (gridGamma b step i))
    (hbin : ∀ i j p, i ∈ Finset.range N → j ∈ Finset.range N →
      p ∈ primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)) →
      p ∈ primeExponentBin x (gridPoint b step j) (gridPoint b step (j + 1)) → i = j) :
    (primeDyadicFinset x).card + (cofactorBinPairFinset x b step N (gridGamma b step)).card ≤
      (roughDyadicFinset x b).card := by
  let P := primeDyadicFinset x
  let S := cofactorBinPairFinset x b step N (gridGamma b step)
  let prodFn : (Σ i : ℕ, Σ _p : ℕ, ℕ) → ℕ := fun z => z.2.1 * z.2.2
  let I : Finset ℕ := S.image prodFn
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hprimeMap : P ⊆ roughDyadicFinset x b := by
    intro n hn
    have h := prime_dyadic_subset_rough hx1 hb
    exact h hn
  have hprodMap : I ⊆ roughDyadicFinset x b := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    exact cofactorBinPairFinset_mapsTo hxpos N (gridGamma b step)
      hparams hz
  have hprodInj : Set.InjOn prodFn (S : Set (Σ i : ℕ, Σ _p : ℕ, ℕ)) :=
    cofactorBinPairFinset_product_injective N (gridGamma b step) hparams hbin
  have hImageCard : I.card = S.card := by
    exact (Finset.card_image_iff.mpr hprodInj)
  have hdisj : Disjoint P I := by
    apply Finset.disjoint_left.mpr
    intro n hnP hnI
    rcases Finset.mem_filter.mp hnP with ⟨_, hnprime⟩
    rcases Finset.mem_image.mp hnI with ⟨z, hz, rfl⟩
    rcases z with ⟨i, ⟨p, m⟩⟩
    have hOuter : ⟨i, ⟨p, m⟩⟩ ∈ (Finset.range N).sigma (fun i =>
        cofactorPairFinset x (gridGamma b step i)
          (primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)))) := by
      simpa [S, cofactorBinPairFinset] using hz
    rcases Finset.mem_sigma.mp hOuter with ⟨hi, hInner⟩
    have hInner' : (⟨p, m⟩ : Σ _p : ℕ, ℕ) ∈
        cofactorPairFinset x (gridGamma b step i)
          (primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1))) := hInner
    rcases Finset.mem_sigma.mp hInner' with ⟨hpBin, hm⟩
    have hpdata := hparams i hi p hpBin
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hpdata.1.pos
    have hpUpper := primeExponentBin_bounds hxpos.le hpBin
    have hu : gridPoint b step (i + 1) < 1 :=
      lt_of_le_of_lt (gridPoint_mono hstep (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
        (by linarith [hEnd])
    have hpowlt : x ^ (gridPoint b step (i + 1)) < x := by
      simpa only [Real.rpow_one] using
        Real.rpow_lt_rpow_of_exponent_lt hx1 hu
    have hpx : (p : ℝ) < x := lt_of_le_of_lt hpUpper.2 hpowlt
    have hpx' : (1 : ℝ) * p < x := by simpa using hpx
    have hygt : 1 < x / p := (lt_div_iff₀ hpR).2 hpx'
    have hfloorY : 1 ≤ ⌊x / p⌋₊ :=
      Nat.le_floor (by exact_mod_cast (le_of_lt hygt))
    have hmIoc : m ∈ Finset.Ioc ⌊x / (p : ℝ)⌋₊ ⌊2 * x / p⌋₊ := by
      simpa using (Finset.mem_filter.mp hm).1
    have hmNat : ⌊x / (p : ℝ)⌋₊ < m := (Finset.mem_Ioc.mp hmIoc).1
    have hmNext : ⌊x / (p : ℝ)⌋₊ + 1 ≤ m := Nat.succ_le_of_lt hmNat
    have hmge : 2 ≤ m := by omega
    have hpPrime := hpdata.1
    have hpdiv : p ∣ p * m := ⟨m, rfl⟩
    have hpeq : p = p * m :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hnprime).mp hpdiv
    have hmone : 1 = m := Nat.mul_left_cancel hpPrime.pos (by simpa using hpeq)
    omega
  have hcardUnion : (P ∪ I).card = P.card + S.card := by
    rw [Finset.card_union_of_disjoint hdisj, hImageCard]
  have hsub : P ∪ I ⊆ roughDyadicFinset x b := Finset.union_subset hprimeMap hprodMap
  calc
    P.card + S.card = (P ∪ I).card := hcardUnion.symm
    _ ≤ (roughDyadicFinset x b).card := Finset.card_le_card hsub

lemma cofactorBins_composite_limit {b B eps : ℝ} (N : ℕ) (hN : 0 < N)
    (hb : 0 < b) (hbB : b < B) (hB : B < 1 / 2)
    (hIH : ∀ i ∈ Finset.range N,
      LowerCountStatement (gridGamma b ((B - b) / (N : ℝ)) i)) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop,
      (∑ i ∈ Finset.range N,
        gridLowerCoeff leastFactorDensity b B N i *
          (Real.log (gridPoint b ((B - b) / (N : ℝ)) (i + 1)) -
            Real.log (gridPoint b ((B - b) / (N : ℝ)) i))) - eps ≤
        L x / x *
          (cofactorBinPairFinset x b ((B - b) / (N : ℝ)) N
            (gridGamma b ((B - b) / (N : ℝ)))).card := by
  let step : ℝ := (B - b) / (N : ℝ)
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hstepPos : 0 < step := by dsimp [step]; exact div_pos (sub_pos.mpr hbB) hNposR
  have hgridEnd : gridPoint b step N = B := by
    dsimp [gridPoint, step]
    field_simp [ne_of_gt hNposR]
    ring
  have hEnd : gridPoint b step N < 1 / 2 := by rw [hgridEnd]; exact hB
  let A : ℕ → ℝ := fun i => gridPoint b step i
  let U : ℕ → ℝ := fun i => gridPoint b step (i + 1)
  let den : ℕ → ℝ := fun i => 1 - A i
  let R : ℕ → ℝ := fun i => Real.log (U i) - Real.log (A i)
  let D : ℕ → ℝ := fun i => roughDensity (gridGamma b step i) 1
  let T : ℝ := ∑ i ∈ Finset.range N, R i / den i
  let delta : ℝ := min (1 / 2 : ℝ) (eps / (4 * (T + 1)))
  let cdelta : ℕ → ℝ := fun i => (D i - delta) / den i
  let Sfull : ℝ := ∑ i ∈ Finset.range N,
    gridLowerCoeff leastFactorDensity b B N i * R i
  let Sdelta : ℝ := ∑ i ∈ Finset.range N, cdelta i * R i
  have hA_mem : ∀ i ∈ Finset.range N, A i ∈ Set.Icc b B := by
    intro i hi
    have hiLe : i ≤ N := Nat.le_of_lt (Finset.mem_range.mp hi)
    have hmem := gridPoint_mem_Icc hbB.le hN hiLe
    simpa [A, step] using hmem
  have hU_mem : ∀ i ∈ Finset.range N, U i ∈ Set.Icc b B := by
    intro i hi
    have hiLe : i + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hmem := gridPoint_mem_Icc hbB.le hN hiLe
    simpa [U, step] using hmem
  have hApos : ∀ i ∈ Finset.range N, 0 < A i := by
    intro i hi
    exact lt_of_lt_of_le hb (hA_mem i hi).1
  have hUpos : ∀ i ∈ Finset.range N, 0 < U i := by
    intro i hi
    exact lt_of_lt_of_le hb (hU_mem i hi).1
  have hAU : ∀ i ∈ Finset.range N, A i < U i := by
    intro i hi
    have hs := gridPoint_succ b step i
    dsimp [A, U]
    nlinarith [hs, hstepPos]
  have hdenPos : ∀ i ∈ Finset.range N, 0 < den i := by
    intro i hi
    have hAi := (hA_mem i hi).2
    dsimp [den]
    linarith [hB]
  have hRpos : ∀ i ∈ Finset.range N, 0 < R i := by
    intro i hi
    dsimp [R]
    exact sub_pos.mpr (Real.log_lt_log (hApos i hi) (hAU i hi))
  have hTpos : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (hRpos i hi).le (hdenPos i hi).le
  have hfullCoeff : ∀ i ∈ Finset.range N,
      gridLowerCoeff leastFactorDensity b B N i = D i / den i := by
    intro i hi
    have hUiLt : U i < 1 := lt_of_le_of_lt (hU_mem i hi).2 (lt_trans hB (by norm_num))
    have hAiLt : A i < 1 := lt_of_le_of_lt (hA_mem i hi).2 (lt_trans hB (by norm_num))
    have hgridCoeff := gridLowerCoeff_density_eq N hN i hAiLt hUiLt
    dsimp [D, den, A, U]
    rw [← hgridEnd]
    exact hgridCoeff
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    apply lt_min (by norm_num)
    positivity
  have hdeltaLt : delta < 1 := by
    dsimp [delta]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hdeltaBound : delta ≤ eps / (4 * (T + 1)) := by
    dsimp [delta]
    exact min_le_right _ _
  have hdeltaT : delta * T ≤ eps / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hdeltaBound hTpos
    have hden : 0 < 4 * (T + 1) := by positivity
    have hfrac : (eps / (4 * (T + 1))) * T ≤ eps / 4 := by
      field_simp [ne_of_gt hden]
      nlinarith [hTpos, heps]
    exact le_trans hmul hfrac
  have hSdeltaEq : Sdelta = Sfull - delta * T := by
    dsimp [Sdelta, Sfull, T, cdelta]
    have hterms : ∀ i ∈ Finset.range N,
        (D i - delta) / den i * R i =
          gridLowerCoeff leastFactorDensity b B N i * R i - delta * (R i / den i) := by
      intro i hi
      rw [hfullCoeff i hi]
      have hden : den i ≠ 0 := ne_of_gt (hdenPos i hi)
      field_simp [hden]
      <;> ring
    calc
      (∑ i ∈ Finset.range N, (D i - delta) / den i * R i) =
          ∑ i ∈ Finset.range N,
            (gridLowerCoeff leastFactorDensity b B N i * R i - delta * (R i / den i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterms i hi
      _ = (∑ i ∈ Finset.range N, gridLowerCoeff leastFactorDensity b B N i * R i) -
            ∑ i ∈ Finset.range N, delta * (R i / den i) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ Finset.range N, gridLowerCoeff leastFactorDensity b B N i * R i) -
            delta * ∑ i ∈ Finset.range N, R i / den i := by
        rw [← Finset.mul_sum]
  have hMassTend : Tendsto
      (fun x : ℝ => ∑ i ∈ Finset.range N,
        cdelta i * scaledPrimeReciprocalInterval x (A i) (U i))
      atTop (nhds Sdelta) := by
    apply tendsto_finsetSum
    intro i hi
    have ha := hApos i hi
    have hab : A i ≤ U i := le_of_lt (hAU i hi)
    have ht := scaledPrimeReciprocalInterval_tendsto ha hab
    simpa [Sdelta, mul_comm] using (ht.mul_const (cdelta i))
  have hMassEvent : ∀ᶠ x : ℝ in atTop,
      Sdelta - eps / 4 ≤ ∑ i ∈ Finset.range N,
        cdelta i * scaledPrimeReciprocalInterval x (A i) (U i) := by
    have hnear : Sdelta - eps / 4 < Sdelta := by linarith
    exact (hMassTend.eventually (Ioi_mem_nhds hnear)).mono fun x hx => le_of_lt hx
  have hpairLower := cofactorBins_lower N hN hb hstepPos hEnd hIH hdeltaPos hdeltaLt
  filter_upwards [hMassEvent, hpairLower, eventually_gt_atTop (2 : ℝ)]
      with x hMass hpairLow hx2
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := Real.log_pos (by linarith : 1 < x)
  have hfactor : 0 ≤ L x / x := div_nonneg hLpos.le hxpos.le
  have hscaleEq : (L x / x) *
      (∑ i ∈ Finset.range N,
        (roughDensity (gridGamma b step i) 1 - delta) * x /
          ((1 - gridPoint b step i) * L x) *
            scaledPrimeReciprocalInterval x (gridPoint b step i)
              (gridPoint b step (i + 1))) =
      ∑ i ∈ Finset.range N,
        cdelta i * scaledPrimeReciprocalInterval x (A i) (U i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hden : 0 < 1 - gridPoint b step i := hdenPos i hi
    have hdenNe : 1 - gridPoint b step i ≠ 0 := ne_of_gt hden
    have hxNe : x ≠ 0 := ne_of_gt hxpos
    have hLNe : L x ≠ 0 := ne_of_gt hLpos
    dsimp [cdelta, D, den, A, U]
    field_simp [hxNe, hLNe, hdenNe]
    <;> ring
  have hpairNorm :
      (∑ i ∈ Finset.range N,
        cdelta i * scaledPrimeReciprocalInterval x (A i) (U i)) ≤
        (L x / x) * ((cofactorBinPairFinset x b step N (gridGamma b step)).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hpairLow hfactor
    rw [hscaleEq] at hmul
    exact hmul
  have hfullBound : Sfull - eps / 2 ≤
      (L x / x) * ((cofactorBinPairFinset x b step N (gridGamma b step)).card : ℝ) := by
    have hsmall : Sfull - eps / 4 ≤ Sdelta := by
      rw [hSdeltaEq]
      linarith [hdeltaT]
    have h := le_trans hMass hpairNorm
    linarith [hsmall]
  change Sfull - eps ≤
    (L x / x) * ((cofactorBinPairFinset x b step N (gridGamma b step)).card : ℝ)
  linarith

lemma primePairCountEvent {b step : ℝ} (N : ℕ) (hb0 : 0 < b) (hb : b < 1)
    (hstep : 0 ≤ step) (hN : 0 < N) (hEnd : gridPoint b step N < 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      (primeDyadicFinset x).card + (cofactorBinPairFinset x b step N (gridGamma b step)).card ≤
        (roughDyadicFinset x b).card := by
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hparams : ∀ i ∈ Finset.range N, ∀ p ∈
      primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)),
      p.Prime ∧ x ^ b < (p : ℝ) ∧ (p : ℝ) ≤ (x / p) ^ (gridGamma b step i) := by
    intro i hi p hp
    have hpdata := primeExponentBin_bounds hxpos.le hp
    have hiLower : b ≤ gridPoint b step i := by
      calc
        b = gridPoint b step 0 := (gridPoint_zero b step).symm
        _ ≤ gridPoint b step i := gridPoint_mono hstep (Nat.zero_le i)
    have hiUpper : gridPoint b step i ≤ gridPoint b step N :=
      gridPoint_mono hstep (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hi1Lower : b ≤ gridPoint b step (i + 1) := by
      calc
        b = gridPoint b step 0 := (gridPoint_zero b step).symm
        _ ≤ gridPoint b step (i + 1) := gridPoint_mono hstep (Nat.zero_le (i + 1))
    have hi1Upper : gridPoint b step (i + 1) ≤ gridPoint b step N :=
      gridPoint_mono hstep (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    have hpow : x ^ b ≤ x ^ (gridPoint b step i) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le hiLower
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have huPos : 0 < gridPoint b step (i + 1) := lt_of_lt_of_le hb0 hi1Lower
    have huLt : gridPoint b step (i + 1) < 1 :=
      lt_of_le_of_lt hi1Upper (by linarith [hEnd])
    have hthreshold := cofactor_threshold hx1 huPos huLt hpPrime.pos hpdata.2
    have hthreshold' : (p : ℝ) ≤ (x / p) ^ (gridGamma b step i) := by
      dsimp [gridGamma]
      exact hthreshold
    exact ⟨hpPrime, lt_of_le_of_lt hpow hpdata.1, hthreshold'⟩
  have hbin : ∀ i j p, i ∈ Finset.range N → j ∈ Finset.range N →
      p ∈ primeExponentBin x (gridPoint b step i) (gridPoint b step (i + 1)) →
      p ∈ primeExponentBin x (gridPoint b step j) (gridPoint b step (j + 1)) → i = j := by
    intro i j p hi hj hpi hpj
    exact primeExponentBins_disjoint hx1 hstep hi hj hpi hpj
  exact prime_and_pair_count_le_rough N hx hb hstep hN hEnd hparams hbin

lemma roughDyadicLower_of_ih {b : ℝ} (hC : ClassicalInputs) (hDI : DensityIntegralIdentity)
    (hb : 0 < b) (hbOne : b < 1)
    (hIH : ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      ⌊1 / gamma⌋₊ < ⌊1 / b⌋₊ → LowerCountStatement gamma) :
    LowerCountStatement b := by
  intro eps heps
  by_cases hbHalf : 1 / 2 ≤ b
  · let eps0 : ℝ := min eps (1 / 2)
    have heps0 : 0 < eps0 := by dsimp [eps0]; positivity
    have heps0lt : eps0 < 1 := by
      dsimp [eps0]
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have heps0le : eps0 ≤ eps := by dsimp [eps0]; exact min_le_left _ _
    have hbase := roughDyadicLower_base hC hbHalf hbOne heps0 heps0lt
    filter_upwards [hbase] with x hx
    have hx' : roughDensity b 1 - eps0 ≤
        L x / x * (roughDyadicFinset x b).card := by
      simpa [roughDyadicFinset] using hx
    linarith
  · have hbHalf : b < 1 / 2 := lt_of_not_ge hbHalf
    let eps0 : ℝ := min eps (1 / 2)
    have heps0 : 0 < eps0 := by dsimp [eps0]; positivity
    have heps0le : eps0 ≤ eps := by dsimp [eps0]; exact min_le_left _ _
    have heps0half : eps0 ≤ 1 / 2 := by dsimp [eps0]; exact min_le_right _ _
    let gap : ℝ := 1 / 2 - b
    let tau : ℝ := min (gap / 2) (eps0 / 100)
    let B : ℝ := 1 / 2 - tau
    have hgap : 0 < gap := by dsimp [gap]; linarith
    have htau : 0 < tau := by
      dsimp [tau]
      apply lt_min
      · positivity
      · positivity
    have htauGap : tau ≤ gap / 2 := by dsimp [tau]; exact min_le_left _ _
    have htauEps : tau ≤ eps0 / 100 := by dsimp [tau]; exact min_le_right _ _
    have hBgtb : b < B := by
      dsimp [B]
      dsimp [gap] at htauGap
      linarith
    have hBhalf : B < 1 / 2 := by dsimp [B]; linarith
    have hBthird : 1 / 3 < B := by
      have htauSmall : tau ≤ (1 : ℝ) / 200 := by
        calc
          tau ≤ eps0 / 100 := htauEps
          _ ≤ (1 / 2 : ℝ) / 100 := by gcongr
          _ = 1 / 200 := by norm_num
      dsimp [B]
      linarith
    have hTail := tail_density_integral_le hBthird hBhalf
    have hTailSmall : 6 * (1 / 2 - B) ≤ eps0 / 4 := by
      dsimp [B]
      have h := htauEps
      norm_num at h ⊢
      nlinarith
    have hSplit := densityIntegral_split hb hBgtb hBthird hBhalf
    have hDensity : roughDensity b 1 =
        1 + (∫ a : ℝ in b..B, leastFactorDensity a / a) +
          (∫ a : ℝ in B..(1 / 2 : ℝ), roughDensity a (1 - a) / a) := by
      have hIdentity := hDI b hb hbHalf
      rw [hSplit] at hIdentity
      linarith
    have hGcont := leastFactorDensity_continuousOn hb hBhalf (le_of_lt hBgtb)
    have hGnonneg : ∀ a ∈ Set.Icc b B, 0 ≤ leastFactorDensity a := by
      intro a ha
      have haIcc := Set.mem_Icc.mp ha
      have haPos : 0 < a := lt_of_lt_of_le hb haIcc.1
      have hden : 0 < 1 - a := by linarith [haIcc.2, hBhalf]
      have hgamma : 0 < a / (1 - a) := div_pos haPos hden
      unfold leastFactorDensity
      have hD := roughDensity_one_ge_one hgamma
      exact div_nonneg (by linarith [hD]) hden.le
    obtain ⟨N, hN, hGrid⟩ := exists_grid_lower_sum hb hBgtb hBhalf hGcont hGnonneg
      (by positivity : 0 < eps0 / 8)
    let step : ℝ := (B - b) / (N : ℝ)
    have hstepPos : 0 < step := by
      dsimp [step]
      exact div_pos (sub_pos.mpr hBgtb) (by exact_mod_cast hN)
    have hgridEnd : gridPoint b step N = B := by
      dsimp [gridPoint, step]
      field_simp [ne_of_gt (by exact_mod_cast hN : 0 < (N : ℝ))]
      ring
    have hIHgrid : ∀ i ∈ Finset.range N, LowerCountStatement (gridGamma b step i) := by
      intro i hi
      have hA : b ≤ gridPoint b step i := by
        calc
          b = gridPoint b step 0 := (gridPoint_zero b step).symm
          _ ≤ gridPoint b step i := gridPoint_mono hstepPos.le (Nat.zero_le i)
      have hU : b ≤ gridPoint b step (i + 1) := by
        calc
          b = gridPoint b step 0 := (gridPoint_zero b step).symm
          _ ≤ gridPoint b step (i + 1) := gridPoint_mono hstepPos.le (Nat.zero_le (i + 1))
      have hUend : gridPoint b step (i + 1) ≤ B := by
        rw [← hgridEnd]
        exact gridPoint_mono hstepPos.le
          (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      have huPos : 0 < gridPoint b step (i + 1) := lt_of_lt_of_le hb hU
      have huOne : gridPoint b step (i + 1) < 1 :=
        lt_of_le_of_lt hUend (by linarith [hBhalf])
      have hgammaPos : 0 < gridGamma b step i := by
        dsimp [gridGamma]
        exact div_pos huPos (by linarith [hBhalf, hUend])
      have hgammaOne : gridGamma b step i < 1 := by
        dsimp [gridGamma]
        apply (div_lt_one (by linarith [hBhalf, hUend])).2
        linarith [hBhalf, hUend]
      have hInvGamma : 1 / (gridGamma b step i) =
          1 / (gridPoint b step (i + 1)) - 1 := by
        dsimp [gridGamma]
        field_simp [ne_of_gt huPos, ne_of_gt (by linarith [hBhalf, hUend] :
          0 < 1 - gridPoint b step (i + 1))]
        <;> ring
      have hInvMono : 1 / (gridPoint b step (i + 1)) ≤ 1 / b :=
        one_div_le_one_div_of_le hb hU
      have hfloorTop : 1 / b < (⌊1 / b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hInvLt : 1 / (gridGamma b step i) < (⌊1 / b⌋₊ : ℝ) := by
        rw [hInvGamma]
        linarith
      have hInvPos : 0 < 1 / (gridGamma b step i) := by positivity
      have hfloorLt : ⌊1 / (gridGamma b step i)⌋₊ < ⌊1 / b⌋₊ :=
        (Nat.floor_lt hInvPos.le).2 hInvLt
      exact hIH (gridGamma b step i) hgammaPos hgammaOne hfloorLt
    have hComp := cofactorBins_composite_limit N hN hb hBgtb hBhalf hIHgrid
      (by positivity : 0 < eps0 / 8)
    have hPrime := primeDyadicNormalizedLower hC (by positivity : 0 < eps0 / 4)
      (by linarith [heps0half] : eps0 / 4 < 1)
    have hPrimePair := primePairCountEvent N hb hbOne hstepPos.le hN
      (by rw [hgridEnd]; exact hBhalf)
    filter_upwards [hComp, hPrime, hPrimePair, eventually_gt_atTop (2 : ℝ)]
      with x hCompX hPrimeX hPrimePairX hx
    have hx1 : 1 < x := by linarith
    have hxpos : 0 < x := by linarith
    have hLpos : 0 < L x := Real.log_pos hx1
    have hfactor : 0 ≤ L x / x := div_nonneg hLpos.le hxpos.le
    have hPrimePairCast :
        ((primeDyadicFinset x).card : ℝ) +
          ((cofactorBinPairFinset x b step N (gridGamma b step)).card : ℝ) ≤
            ((roughDyadicFinset x b).card : ℝ) := by exact_mod_cast hPrimePairX
    have hPrimePairNorm := mul_le_mul_of_nonneg_left hPrimePairCast hfactor
    have hPrimePairNorm' :
        L x / x * (primeDyadicFinset x).card +
          L x / x * (cofactorBinPairFinset x b step N (gridGamma b step)).card ≤
            L x / x * (roughDyadicFinset x b).card := by
      simpa [mul_add] using hPrimePairNorm
    have hCompInt : (∫ a : ℝ in b..B, leastFactorDensity a / a) - eps0 / 4 ≤
        L x / x * (cofactorBinPairFinset x b step N (gridGamma b step)).card := by
      calc
        (∫ a : ℝ in b..B, leastFactorDensity a / a) - eps0 / 4 =
            ((∫ a : ℝ in b..B, leastFactorDensity a / a) - eps0 / 8) - eps0 / 8 := by ring
        _ ≤ (∑ i ∈ Finset.range N,
              gridLowerCoeff leastFactorDensity b B N i *
                (Real.log (gridPoint b step (i + 1)) - Real.log (gridPoint b step i))) - eps0 / 8 :=
              by simpa [step] using hGrid
        _ ≤ L x / x * (cofactorBinPairFinset x b step N (gridGamma b step)).card := hCompX
    have hCombined :
        1 - eps0 / 4 +
          ((∫ a : ℝ in b..B, leastFactorDensity a / a) - eps0 / 4) ≤
            L x / x * (roughDyadicFinset x b).card := by
      have hAdd := add_le_add hPrimeX hCompInt
      have hPrimePairNorm'' :
          L x / x * ((Finset.filter Nat.Prime
              (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊)).card : ℝ) +
            L x / x * (cofactorBinPairFinset x b step N (gridGamma b step)).card ≤
              L x / x * (roughDyadicFinset x b).card := by
        simpa [primeDyadicFinset] using hPrimePairNorm'
      linarith [hAdd, hPrimePairNorm'']
    have hWanted : roughDensity b 1 - eps0 ≤
        L x / x * (roughDyadicFinset x b).card := by
      rw [hDensity]
      linarith [hTail, hTailSmall, hCombined]
    have hWanted' : roughDensity b 1 - eps ≤
        L x / x * (roughDyadicFinset x b).card := by linarith [hWanted, heps0le]
    exact hWanted'

theorem roughDyadicDensityLowerTask_of_densityIntegralIdentity
    (hDI : DensityIntegralIdentity) : RoughDyadicDensityLowerTask := by
  intro hC b hb hbOne
  have hRank : ∀ n : ℕ, ∀ b : ℝ, 0 < b → b < 1 → ⌊1 / b⌋₊ = n →
      LowerCountStatement b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hb hbOne hfloor
      apply roughDyadicLower_of_ih hC hDI hb hbOne
      intro gamma hgamma hgammaOne hrank
      have hrank' : ⌊1 / gamma⌋₊ < n := by rw [← hfloor]; exact hrank
      exact ih ⌊1 / gamma⌋₊ hrank' gamma hgamma hgammaOne rfl
  exact hRank ⌊1 / b⌋₊ b hb hbOne rfl

theorem densityIntegralIdentity_proof : DensityIntegralIdentity := by
  intro b hb hbHalf
  exact Erdos821.P8Int.DensityIntegralTask_proof b hb hbHalf

theorem roughDyadicDensityLowerTask_proof : RoughDyadicDensityLowerTask := by
  exact roughDyadicDensityLowerTask_of_densityIntegralIdentity densityIntegralIdentity_proof

end Erdos821.P8Low
