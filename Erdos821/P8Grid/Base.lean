import Erdos821.Blueprint.Proxy
import OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
import Erdos821.P8.GridAbsorption
import Erdos821.P8.SimplexInflation
import Erdos821.P8Tail.TailRestriction

noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Grid
open Blueprint Blueprint.Analytic

/-- Task: uniform prime-list counting limit on a compact parameter region.
The full real-endpoint cell convention is (Y, exp(delta) Y]. -/
def RoughCellDensityTask : Prop :=
  ClassicalInputs → ∀ b wMax gap S : ℝ,
    0 < b → 0 < wMax → 0 < gap → 0 < S →
    ∀ eps : ℝ, 0 < eps → ∀ᶠ x : ℝ in atTop, ∀ gamma w : ℝ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax →
      (((Finset.Ioc ⌊x ^ w⌋₊ ⌊Real.exp (L x ^ (-S)) * x ^ w⌋₊).filter
        (rough (x ^ gamma))).card : ℝ) ≤
        (roughDensity gamma w + eps) * L x ^ (-S) * x ^ w / L x

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

theorem scaledPrimeReciprocalInterval_eq_log {a b x : ℝ}
    (hx : 1 < x) (ha : 0 < a) (hab : a ≤ b) :
    scaledPrimeReciprocalInterval x a b =
      Real.log b - Real.log a + Erdos970.Mertens.E₂p (x ^ b) -
        Erdos970.Mertens.E₂p (x ^ a) := by
  have hx0 : 0 < x := by linarith
  have hb : 0 < b := ha.trans_le hab
  have hpow : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hab
  have hsum := prime_interval_reciprocal_sum (x ^ a) (x ^ b) (Nat.floor_mono hpow)
  rw [scaledPrimeReciprocalInterval, hsum,
    reciprocalPrimeSum_eq (x ^ b), reciprocalPrimeSum_eq (x ^ a),
    Real.log_rpow hx0 b, Real.log_rpow hx0 a,
    Real.log_mul hb.ne' (Real.log_pos hx).ne',
    Real.log_mul ha.ne' (Real.log_pos hx).ne']
  ring

/-- Mertens' formula gives an interval estimate uniform over positive exponents in a compact
range, since every endpoint power tends to infinity uniformly from below. -/
theorem scaledPrimeReciprocalInterval_uniform_upper
    {b eps : ℝ} (hb : 0 < b) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ a c : ℝ, b ≤ a → a ≤ c →
      scaledPrimeReciprocalInterval x a c ≤ Real.log c - Real.log a + eps := by
  have hE := mertens_remainder_tendsto
  have hepsHalf : 0 < eps / 2 := by positivity
  have hEsmall : ∀ᶠ y : ℝ in atTop, |Erdos970.Mertens.E₂p y| < eps / 2 := by
    have hu := hE.eventually (Iio_mem_nhds hepsHalf)
    have hneg : -eps / 2 < 0 := by linarith
    have hl := hE.eventually (Ioi_mem_nhds hneg)
    filter_upwards [hu, hl] with y hyu hyl
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hEsmall
  have hpowTop : Tendsto (fun x : ℝ => x ^ b) atTop atTop := tendsto_rpow_atTop hb
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1
    (hpowTop.eventually (eventually_ge_atTop Y₀))
  refine Filter.eventually_atTop.2 ⟨max X₀ 2, ?_⟩
  intro x hx
  have hx₂ : 2 ≤ x := le_trans (le_max_right X₀ 2) hx
  have hxgt : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hxY : Y₀ ≤ x ^ b := hX₀ x (le_trans (le_max_left X₀ 2) hx)
  intro a c ha hac
  have haPow : x ^ b ≤ x ^ a :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) ha
  have hcPow : x ^ a ≤ x ^ c :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hac
  have haErr := hY₀ (x ^ a) (hxY.trans haPow)
  have hcErr := hY₀ (x ^ c) (hxY.trans (haPow.trans hcPow))
  rw [scaledPrimeReciprocalInterval_eq_log hxgt (lt_of_lt_of_le hb ha) hac]
  rcases abs_lt.mp hcErr with ⟨hcLo, hcHi⟩
  rcases abs_lt.mp haErr with ⟨haLo, haHi⟩
  linarith

theorem log_interval_le_length_div {b a c : ℝ}
    (hb : 0 < b) (hba : b ≤ a) (hac : a ≤ c) :
    Real.log c - Real.log a ≤ (c - a) / b := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hc : 0 < c := ha.trans_le hac
  have hlog := Real.log_le_sub_one_of_pos (div_pos hc ha)
  have hdivlog : Real.log (c / a) = Real.log c - Real.log a := by
    rw [Real.log_div hc.ne' ha.ne']
  have hca : 0 ≤ c - a := by linarith
  calc
    Real.log c - Real.log a = Real.log (c / a) := hdivlog.symm
    _ ≤ c / a - 1 := hlog
    _ = (c - a) / a := by field_simp
    _ ≤ (c - a) / b := (div_le_div_iff₀ ha hb).2 (by nlinarith)

theorem log_interval_ge_length_div_upper {a c U : ℝ}
    (ha : 0 < a) (hac : a ≤ c) (hcU : c ≤ U) :
    (c - a) / U ≤ Real.log c - Real.log a := by
  have hc : 0 < c := ha.trans_le hac
  have hU : 0 < U := hc.trans_le hcU
  have hca : 0 ≤ c - a := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha hc)
  have hlogdiv : Real.log (a / c) = Real.log a - Real.log c :=
    Real.log_div ha.ne' hc.ne'
  have heq : 1 - a / c = (c - a) / c := by field_simp
  have hsmall : (c - a) / c ≤ Real.log c - Real.log a := by
    calc
      (c - a) / c = 1 - a / c := heq.symm
      _ ≤ -Real.log (a / c) := by linarith [hlog]
      _ = Real.log c - Real.log a := by rw [hlogdiv]; ring
  calc
    (c - a) / U ≤ (c - a) / c :=
      (div_le_div_iff₀ hU hc).2 (by nlinarith [hca, hcU])
    _ ≤ Real.log c - Real.log a := hsmall

theorem pow_add_diff_le {a e : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (n : ℕ) :
    (a + e) ^ n - a ^ n ≤ (n : ℝ) * e * (1 + a + e) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      let C : ℝ := 1 + a + e
      have hCnonneg : 0 ≤ C := by dsimp [C]; linarith
      have hC1 : 1 ≤ C := by dsimp [C]; linarith
      have haC : a ≤ C := by dsimp [C]; linarith
      have hBpow : (a + e) ^ n ≤ C ^ n := by
        apply pow_le_pow_left₀ (by positivity : 0 ≤ a + e)
        dsimp [C]
        linarith
      have hCpow : 0 ≤ C ^ n := pow_nonneg hCnonneg n
      calc
        (a + e) ^ (n + 1) - a ^ (n + 1) =
            (a + e) ^ n * e + a * ((a + e) ^ n - a ^ n) := by
              rw [pow_succ, pow_succ]
              ring
        _ ≤ C ^ n * e + a * ((n : ℝ) * e * C ^ n) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBpow he
              · exact mul_le_mul_of_nonneg_left ih ha
        _ = (1 + a * (n : ℝ)) * (e * C ^ n) := by ring
        _ ≤ ((n : ℝ) + 1) * C * (e * C ^ n) := by
              apply mul_le_mul_of_nonneg_right
              · nlinarith [hC1, haC]
              · exact mul_nonneg he hCpow
        _ = (n + 1 : ℕ) * e * (1 + a + e) ^ (n + 1) := by
              simp only [Nat.cast_add, Nat.cast_one, pow_succ, C]
              ring

theorem scaledPrimeReciprocalInterval_uniform_length_upper
    {b eps : ℝ} (hb : 0 < b) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ a c : ℝ, b ≤ a → a ≤ c →
      scaledPrimeReciprocalInterval x a c ≤ (c - a) / b + eps := by
  filter_upwards [scaledPrimeReciprocalInterval_uniform_upper hb heps] with x hx
  intro a c ha hac
  calc
    scaledPrimeReciprocalInterval x a c ≤ Real.log c - Real.log a + eps := hx a c ha hac
    _ ≤ (c - a) / b + eps := by
      linarith [log_interval_le_length_div hb ha hac]

theorem exp_delta_le_quadratic {delta : ℝ}
    (hdelta : 0 ≤ delta) (hdelta_one : delta ≤ 1) :
    Real.exp delta - 1 ≤ delta + delta ^ 2 := by
  have habs : |delta| ≤ 1 := by simpa [abs_of_nonneg hdelta] using hdelta_one
  have h := Real.abs_exp_sub_one_sub_id_le habs
  have hupper := (abs_le.mp h).2
  linarith

theorem scaledPrimeReciprocalRectangle_tendsto {k : ℕ}
    (a b : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i) :
    Tendsto (fun x : ℝ => Finset.univ.prod fun i : Fin k =>
      scaledPrimeReciprocalInterval x (a i) (b i))
      atTop (nhds (Finset.univ.prod fun i : Fin k => Real.log (b i) - Real.log (a i))) := by
  classical
  apply tendsto_finsetProd (Finset.univ : Finset (Fin k))
  intro i hi
  exact scaledPrimeReciprocalInterval_tendsto (ha i) (hab i)

theorem card_equiv_finset {α : Type*} [DecidableEq α] (s : Finset α) {k : ℕ}
    (hcard : s.card = k) : Fintype.card (Fin k ≃ {a // a ∈ s}) = Nat.factorial k := by
  let e : {a // a ∈ s} ≃ Fin k := s.equivFinOfCardEq hcard
  have h : Fintype.card (Fin k ≃ {a // a ∈ s}) =
      Nat.factorial (Fintype.card (Fin k)) := Fintype.card_equiv e.symm
  simpa using h

theorem prod_equiv_finset {α β : Type*} [DecidableEq α] [CommMonoid β]
    (s : Finset α) (f : α → β) {k : ℕ}
    (e : Fin k ≃ {a // a ∈ s}) :
    (∏ i : Fin k, f (e i).val) = ∏ a ∈ s, f a := by
  calc
    (∏ i : Fin k, f (e i).val) = ∏ a : {a // a ∈ s}, f a.val :=
      Fintype.prod_equiv e _ _ (fun i => rfl)
    _ = ∏ a ∈ s, f a := Finset.prod_coe_sort s f

theorem reciprocal_square_tail_finset (N M : ℕ) (hN : 2 ≤ N) :
    (∑ d ∈ Finset.Icc N M, (1 / (d : ℝ) ^ 2)) ≤ 1 / ((N : ℝ) - 1) := by
  by_cases hNM : N ≤ M
  · have htel : Finset.sum (Finset.Icc N M) (fun d : ℕ =>
        ((d : ℝ) - 1)⁻¹ - (d : ℝ)⁻¹) =
        ((N : ℝ) - 1)⁻¹ - (M : ℝ)⁻¹ := by
      induction M, hNM using Nat.le_induction with
      | base => simp
      | succ M hNM ih =>
          have hIcc : Finset.Icc N (M + 1) = insert (M + 1) (Finset.Icc N M) := by
            ext d
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          have hnot : M + 1 ∉ Finset.Icc N M := by
            simp [Finset.mem_Icc]
          rw [hIcc, Finset.sum_insert hnot, ih]
          have hNcast : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
          have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
          have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
          have hMcast : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
          have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
          simp only [Nat.cast_add, Nat.cast_one]
          field_simp [ne_of_gt hN1, ne_of_gt hM0, ne_of_gt hM1]
          ring
    have hterm (d : ℕ) (hd : d ∈ Finset.Icc N M) :
        1 / (d : ℝ) ^ 2 ≤ ((d : ℝ) - 1)⁻¹ - (d : ℝ)⁻¹ := by
      have hdN : N ≤ d := (Finset.mem_Icc.mp hd).1
      have hdp : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
      have hd0 : 0 < (d : ℝ) := by linarith
      have hden : (d : ℝ) * ((d : ℝ) - 1) ≤ (d : ℝ) ^ 2 := by nlinarith
      have hrecip := one_div_le_one_div_of_le (mul_pos hd0 (by linarith)) hden
      have heq : 1 / ((d : ℝ) * ((d : ℝ) - 1)) =
          ((d : ℝ) - 1)⁻¹ - (d : ℝ)⁻¹ := by
        field_simp [ne_of_gt hd0, ne_of_gt (by linarith : 0 < (d : ℝ) - 1)]
        ring
      exact hrecip.trans_eq heq
    calc
      _ ≤ Finset.sum (Finset.Icc N M) (fun d : ℕ =>
          ((d : ℝ) - 1)⁻¹ - (d : ℝ)⁻¹) :=
        Finset.sum_le_sum (fun d hd => hterm d hd)
      _ = ((N : ℝ) - 1)⁻¹ - (M : ℝ)⁻¹ := htel
      _ ≤ 1 / ((N : ℝ) - 1) := by
        have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
        have hNcast : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
        have hNden : 0 < (N : ℝ) - 1 := by linarith
        calc
          ((N : ℝ) - 1)⁻¹ - (M : ℝ)⁻¹ ≤ ((N : ℝ) - 1)⁻¹ := sub_le_self _ (by positivity)
          _ = 1 / ((N : ℝ) - 1) := by ring
  · have hempty : Finset.Icc N M = ∅ := Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hNM)
    simp [hempty]
    omega

theorem densityTerm_nonneg {gamma w : ℝ} (hgamma : 0 < gamma)
    (l : ℕ) : 0 ≤ densityTerm gamma w l := by
  unfold densityTerm
  apply integral_nonneg
  intro t
  dsimp
  split_ifs with h
  · rcases h with ⟨ht, hsum⟩
    have hden : 0 < w - ∑ i, t i := by linarith
    have hprod : 0 ≤ ∏ i, (t i)⁻¹ :=
      Finset.prod_nonneg fun i hi => inv_nonneg.mpr (le_of_lt (hgamma.trans_le (ht i)))
    exact mul_nonneg (inv_nonneg.mpr hden.le) hprod
  · simp

theorem densityTerm_eq_zero_of_length_gt {gamma w : ℝ} {l : ℕ}
    (hl : 2 ≤ l) (hwl : w < (l : ℝ) * gamma) : densityTerm gamma w l = 0 := by
  unfold densityTerm
  have hfun : (fun t : Fin (l - 1) → ℝ =>
      if (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma then
        (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0) = fun _ => (0 : ℝ) := by
    funext t
    split_ifs with h
    · rcases h with ⟨ht, hsum⟩
      have hsumMin : ((l : ℝ) - 1) * gamma ≤ ∑ i : Fin (l - 1), t i := by
        calc
          ((l : ℝ) - 1) * gamma = ∑ i : Fin (l - 1), gamma := by simp [Nat.cast_sub (by omega : 1 ≤ l)]
          _ ≤ ∑ i : Fin (l - 1), t i := Finset.sum_le_sum fun i hi => ht i
      have hlen : (l : ℝ) * gamma ≤ w := by linarith
      linarith
    · rfl
  rw [hfun]
  simp

theorem roughDensity_eq_inv_add_cutoff {gamma w : ℝ} (hgamma : 0 < gamma)
    {K : ℕ} (hK : ⌊w / gamma⌋₊ ≤ K) :
    roughDensity gamma w = w⁻¹ +
      ∑ l ∈ Finset.Icc 2 K, densityTerm gamma w l / (l.factorial : ℝ) := by
  unfold roughDensity
  have hsub : Finset.Icc 2 ⌊w / gamma⌋₊ ⊆ Finset.Icc 2 K :=
    Finset.Icc_subset_Icc_right hK
  have hsum :
      (∑ l ∈ Finset.Icc 2 K, densityTerm gamma w l / (l.factorial : ℝ)) =
        ∑ l ∈ Finset.Icc 2 ⌊w / gamma⌋₊,
          densityTerm gamma w l / (l.factorial : ℝ) := by
    symm
    apply Finset.sum_subset hsub
    intro l hl hln
    have hllow : 2 ≤ l := (Finset.mem_Icc.mp hl).1
    have hlfloor : ⌊w / gamma⌋₊ < l := by
      exact lt_of_not_ge (fun h => hln (Finset.mem_Icc.mpr ⟨hllow,h⟩))
    have hratio : w / gamma < (l : ℝ) := by
      have hfloorlt := Nat.lt_floor_add_one (w / gamma)
      have hfloorplus : ((⌊w / gamma⌋₊ : ℝ) + 1) ≤ (l : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hlfloor)
      exact hfloorlt.trans_le hfloorplus
    have hwl : w < (l : ℝ) * gamma := (div_lt_iff₀ hgamma).1 hratio
    simp [densityTerm_eq_zero_of_length_gt hllow hwl]
  rw [hsum]

theorem roughDensity_ge_inv {gamma w : ℝ} (hgamma : 0 < gamma) :
    w⁻¹ ≤ roughDensity gamma w := by
  unfold roughDensity
  have hsum : 0 ≤ ∑ l ∈ Finset.Icc 2 ⌊w / gamma⌋₊,
      densityTerm gamma w l / (l.factorial : ℝ) := by
    apply Finset.sum_nonneg
    intro l hl
    exact div_nonneg (densityTerm_nonneg hgamma l) (by positivity)
  exact le_add_of_nonneg_right hsum

def simplexDensityIntegrand (gamma w : ℝ) (l : ℕ)
    (t : Fin (l - 1) → ℝ) : ℝ :=
  if (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma then
    (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0

lemma simplexDensityIntegrand_measurable (gamma w : ℝ) (l : ℕ) :
    Measurable (simplexDensityIntegrand gamma w l) := by
  unfold simplexDensityIntegrand
  have hcond : MeasurableSet {t : Fin (l - 1) → ℝ |
      (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma} := by measurability
  exact Measurable.ite hcond (by fun_prop) measurable_const

lemma simplexDensityIntegrand_support_ball {gamma w : ℝ} {l : ℕ}
    {t : Fin (l - 1) → ℝ} (hgamma : 0 < gamma) (hw : gamma < w)
    (hdom : (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma) :
    t ∈ Metric.closedBall (0 : Fin (l - 1) → ℝ) (w + 1) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsum_nonneg : 0 ≤ ∑ i, t i :=
    Finset.sum_nonneg fun i hi => (le_of_lt hgamma).trans (hdom.1 i)
  have hwpos : 0 < w := hgamma.trans hw
  apply (pi_norm_le_iff_of_nonneg (by linarith)).2
  intro i
  have hti_pos : 0 < t i := hgamma.trans_le (hdom.1 i)
  have hti_le_sum : t i ≤ ∑ j, t j :=
    Finset.single_le_sum (fun j hj => (le_of_lt hgamma).trans (hdom.1 j))
      (Finset.mem_univ i)
  have hti_le : t i ≤ w + 1 := by linarith [hdom.2, hti_le_sum]
  rw [Real.norm_eq_abs, abs_of_nonneg hti_pos.le]
  exact hti_le

lemma simplexDensityIntegrand_norm_bound {gamma w : ℝ} {l : ℕ}
    {t : Fin (l - 1) → ℝ} (hl : 2 ≤ l) (hgamma : 0 < gamma)
    (hdom : (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma) :
    ‖simplexDensityIntegrand gamma w l t‖ ≤ gamma⁻¹ ^ l := by
  have hden : gamma ≤ w - ∑ i, t i := by linarith [hdom.2]
  have hden_pos : 0 < w - ∑ i, t i := hgamma.trans_le hden
  have hden_inv : (w - ∑ i, t i)⁻¹ ≤ gamma⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le hgamma hden
  have hti_pos : ∀ i, 0 < t i := fun i => hgamma.trans_le (hdom.1 i)
  have hti_inv : ∀ i, 0 ≤ (t i)⁻¹ ∧ (t i)⁻¹ ≤ gamma⁻¹ := by
    intro i
    constructor
    · exact inv_nonneg.mpr (hti_pos i).le
    · simpa [one_div] using one_div_le_one_div_of_le hgamma (hdom.1 i)
  have hprod : (∏ i, (t i)⁻¹) ≤ gamma⁻¹ ^ (l - 1) := by
    calc
      (∏ i, (t i)⁻¹) ≤ ∏ _i : Fin (l - 1), gamma⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (hti_inv i).1
        · intro i hi
          exact (hti_inv i).2
      _ = gamma⁻¹ ^ (l - 1) := by simp
  have hprod_nonneg : 0 ≤ ∏ i, (t i)⁻¹ :=
    Finset.prod_nonneg fun i hi => (hti_inv i).1
  have hkernel_nonneg : 0 ≤ (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hden_pos.le) hprod_nonneg
  rw [simplexDensityIntegrand, if_pos hdom, Real.norm_eq_abs,
    abs_of_nonneg hkernel_nonneg]
  have hlEq : l - 1 + 1 = l := Nat.sub_add_cancel (by omega)
  calc
    (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ ≤ gamma⁻¹ * gamma⁻¹ ^ (l - 1) :=
      mul_le_mul hden_inv hprod hprod_nonneg (by positivity)
    _ = gamma⁻¹ ^ l := by
      rw [show l = (l - 1) + 1 by omega, pow_succ']
      rw [show l - 1 + 1 - 1 = l - 1 by omega]

lemma simplexDensityIntegrand_integrable {gamma w : ℝ} {l : ℕ}
    (hl : 2 ≤ l) (hgamma : 0 < gamma) (hw : gamma < w) :
    Integrable (simplexDensityIntegrand gamma w l) volume := by
  let K : Set (Fin (l - 1) → ℝ) := Metric.closedBall 0 (w + 1)
  let B : (Fin (l - 1) → ℝ) → ℝ := K.indicator (fun _ => gamma⁻¹ ^ l)
  have hK : volume K ≠ ⊤ :=
    (isCompact_closedBall (0 : Fin (l - 1) → ℝ) (w + 1)).measure_ne_top
  have hBint : Integrable B volume := by
    have hKB : IntegrableOn (fun _ : Fin (l - 1) → ℝ => gamma⁻¹ ^ l) K volume :=
      integrableOn_const (μ := volume) (s := K) (C := gamma⁻¹ ^ l) hK
    exact IntegrableOn.integrable_indicator hKB (Metric.isClosed_closedBall.measurableSet)
  apply Integrable.mono' hBint (simplexDensityIntegrand_measurable gamma w l).aestronglyMeasurable
  apply ae_of_all
  intro t
  by_cases hdom : (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma
  · have htK := simplexDensityIntegrand_support_ball hgamma hw hdom
    simpa [B, K, htK] using simplexDensityIntegrand_norm_bound hl hgamma hdom
  · by_cases htK : t ∈ K
    · simp [simplexDensityIntegrand, B, K, hdom, htK]
      positivity
    · simp [simplexDensityIntegrand, B, K, hdom, htK]

theorem densityTerm_integrand_eq_integral (gamma w : ℝ) (l : ℕ) :
    densityTerm gamma w l = ∫ t : Fin (l - 1) → ℝ, simplexDensityIntegrand gamma w l t := by
  rfl

abbrev PrimeLabel (P : Finset ℕ) := {p : ℕ // p ∈ P}

theorem primeLabelTupleWeight_factor {P : Finset ℕ} {k : ℕ}
    (g : Fin k → PrimeLabel P → ℝ) :
    (∑ f : Fin k → PrimeLabel P, ∏ i, g i (f i)) =
      ∏ i, ∑ p : PrimeLabel P, g i p := by
  classical
  exact (Fintype.prod_sum g).symm

def primeLabelReciprocalIntervalMass (x a b : ℝ) (P : Finset ℕ) : ℝ :=
  ∑ p : PrimeLabel P,
    if p.val ∈ (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime then
      1 / (p.val : ℝ) else 0

theorem primeLabelReciprocalIntervalMass_nonneg (x a b : ℝ) (P : Finset ℕ) :
    0 ≤ primeLabelReciprocalIntervalMass x a b P := by
  classical
  unfold primeLabelReciprocalIntervalMass
  apply Finset.sum_nonneg
  intro p hp
  split_ifs with h
  · have hprime := (Finset.mem_filter.mp h).2
    have hp0 : 0 < (p.val : ℝ) := by exact_mod_cast hprime.pos
    positivity
  · simp

theorem primeLabelReciprocalIntervalMass_le (x a b : ℝ) (P : Finset ℕ) :
    primeLabelReciprocalIntervalMass x a b P ≤ scaledPrimeReciprocalInterval x a b := by
  classical
  let J : Finset ℕ := (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime
  let T : Finset ℕ := P.filter (fun p => p ∈ J)
  let f : ℕ → ℝ := fun p => if p ∈ J then 1 / (p : ℝ) else 0
  change (∑ p : P, f p.val) ≤ _
  rw [Finset.sum_coe_sort P f]
  have hsum : (∑ p ∈ P, f p) =
      ∑ p ∈ T, 1 / (p : ℝ) := by
    simp [T, f, Finset.sum_filter]
  have hsub : T ⊆ J := by
    intro p hp
    exact (Finset.mem_filter.mp (by simpa [T] using hp)).2
  calc
    (∑ p ∈ P, f p) =
        ∑ p ∈ T, 1 / (p : ℝ) := hsum
    _ ≤ ∑ p ∈ J, 1 / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      positivity
    _ = scaledPrimeReciprocalInterval x a b := by
      rfl

theorem primeLabelReciprocalIntervalMass_uniform_length_upper
    {b eps : ℝ} (hb : 0 < b) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ, ∀ a c : ℝ, b ≤ a → a ≤ c →
      primeLabelReciprocalIntervalMass x a c P ≤ (c - a) / b + eps := by
  filter_upwards [scaledPrimeReciprocalInterval_uniform_length_upper hb heps] with x hx
  intro P a c ha hac
  exact (primeLabelReciprocalIntervalMass_le x a c P).trans (hx a c ha hac)

theorem primeLabelReciprocalIntervalMass_uniform_log_upper
    {b eps : ℝ} (hb : 0 < b) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ, ∀ a c : ℝ, b ≤ a → a ≤ c →
      primeLabelReciprocalIntervalMass x a c P ≤ Real.log c - Real.log a + eps := by
  filter_upwards [scaledPrimeReciprocalInterval_uniform_upper hb heps] with x hx
  intro P a c ha hac
  exact (primeLabelReciprocalIntervalMass_le x a c P).trans (hx a c ha hac)

theorem primeLabelTupleRectangleMass_eq {P : Finset ℕ} {k : ℕ}
    (x : ℝ) (a c : Fin k → ℝ) :
    (∑ f : Fin k → PrimeLabel P,
      ∏ i, if (f i).val ∈ (Finset.Ioc ⌊x ^ (a i)⌋₊ ⌊x ^ (c i)⌋₊).filter Nat.Prime
        then 1 / ((f i).val : ℝ) else 0) =
      ∏ i, primeLabelReciprocalIntervalMass x (a i) (c i) P := by
  classical
  simpa [primeLabelReciprocalIntervalMass] using
    (primeLabelTupleWeight_factor (P := P) (k := k)
      (fun i p => if p.val ∈ (Finset.Ioc ⌊x ^ (a i)⌋₊ ⌊x ^ (c i)⌋₊).filter Nat.Prime
        then 1 / (p.val : ℝ) else 0))

def exponentGridEndpoint (x b h : ℝ) (j : ℕ) : ℕ :=
  ⌊x ^ (b + (j : ℝ) * h)⌋₊

def exponentGridCell (x b h : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Ioc (exponentGridEndpoint x b h j) (exponentGridEndpoint x b h (j + 1))

theorem exponentGridEndpoint_mono {x b h : ℝ} (hx : 1 < x) (hh : 0 ≤ h)
    {i j : ℕ} (hij : i ≤ j) :
    exponentGridEndpoint x b h i ≤ exponentGridEndpoint x b h j := by
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le (by linarith)
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  nlinarith [mul_nonneg (sub_nonneg.mpr hij') hh]

theorem exponentGridCell_union_range (x b h : ℝ) (N : ℕ)
    (hx : 1 < x) (hh : 0 ≤ h) :
    (Finset.range N).biUnion (exponentGridCell x b h) =
      Finset.Ioc (exponentGridEndpoint x b h 0) (exponentGridEndpoint x b h N) := by
  induction N with
  | zero => simp [exponentGridCell]
  | succ N ih =>
      have hmono : exponentGridEndpoint x b h N ≤ exponentGridEndpoint x b h (N + 1) :=
        exponentGridEndpoint_mono hx hh (Nat.le_succ N)
      have hmono0 : exponentGridEndpoint x b h 0 ≤ exponentGridEndpoint x b h N :=
        exponentGridEndpoint_mono hx hh (Nat.zero_le N)
      have hsplit :
          Finset.Ioc (exponentGridEndpoint x b h 0) (exponentGridEndpoint x b h (N + 1)) =
            Finset.Ioc (exponentGridEndpoint x b h 0) (exponentGridEndpoint x b h N) ∪
              Finset.Ioc (exponentGridEndpoint x b h N) (exponentGridEndpoint x b h (N + 1)) := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_union]
        omega
      rw [Finset.range_add_one, Finset.biUnion_insert, ih]
      rw [hsplit]
      exact Finset.union_comm _ _

theorem exponentGridLabelMass_le {b h eps : ℝ} (hb : 0 < b) (hh : 0 ≤ h)
    (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ, ∀ j : ℕ,
      primeLabelReciprocalIntervalMass x
        (b + (j : ℝ) * h) (b + ((j + 1 : ℕ) : ℝ) * h) P ≤ h / b + eps := by
  filter_upwards [primeLabelReciprocalIntervalMass_uniform_length_upper hb heps] with x hx
  intro P j
  have hleft : b ≤ b + (j : ℝ) * h := by
    have hj : 0 ≤ (j : ℝ) := by positivity
    linarith [mul_nonneg hj hh]
  have hright : b + (j : ℝ) * h ≤ b + ((j + 1 : ℕ) : ℝ) * h := by
    have hj : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
    nlinarith [mul_nonneg (sub_nonneg.mpr hj) hh]
  have hmass := hx P (b + (j : ℝ) * h) (b + ((j + 1 : ℕ) : ℝ) * h)
    hleft hright
  have hmass' : primeLabelReciprocalIntervalMass x
      (b + (j : ℝ) * h) (b + ((j + 1 : ℕ) : ℝ) * h) P ≤
        (b + ((j : ℝ) + 1) * h - (b + (j : ℝ) * h)) / b + eps := by
    simpa only [Nat.cast_add, Nat.cast_one] using hmass
  calc
    primeLabelReciprocalIntervalMass x (b + (j : ℝ) * h)
        (b + ((j + 1 : ℕ) : ℝ) * h) P ≤
      (b + ((j : ℝ) + 1) * h - (b + (j : ℝ) * h)) / b + eps := hmass'
    _ = (((j : ℝ) + 1) * h - (j : ℝ) * h) / b + eps := by congr 1 <;> ring
    _ = h / b + eps := by congr 1 <;> ring

theorem exponentGridLabel_cover (x b h : ℝ) (N : ℕ) (P : Finset ℕ)
    (hx : 1 < x) (hh : 0 ≤ h)
    (hP : P ⊆ Finset.Ioc (exponentGridEndpoint x b h 0)
      (exponentGridEndpoint x b h N)) :
    ∀ p : PrimeLabel P, ∃ j < N, p.val ∈ exponentGridCell x b h j := by
  intro p
  have hp : p.val ∈ Finset.Ioc (exponentGridEndpoint x b h 0)
      (exponentGridEndpoint x b h N) := hP p.property
  rw [← exponentGridCell_union_range x b h N hx hh] at hp
  rcases Finset.mem_biUnion.mp hp with ⟨j, hj, hjcell⟩
  exact ⟨j, Finset.mem_range.mp hj, hjcell⟩

theorem exponentGridTuple_cover {P : Finset ℕ} {k : ℕ}
    (x b h : ℝ) (N : ℕ) (hx : 1 < x) (hh : 0 ≤ h)
    (hP : P ⊆ Finset.Ioc (exponentGridEndpoint x b h 0)
      (exponentGridEndpoint x b h N)) :
    ∀ f : Fin k → PrimeLabel P, ∃ j : Fin k → ℕ,
      ∀ i, j i < N ∧ (f i).val ∈ exponentGridCell x b h (j i) := by
  intro f
  classical
  choose j hj using fun i : Fin k => exponentGridLabel_cover x b h N P hx hh hP (f i)
  exact ⟨j, hj⟩

theorem integral_Ioc_inv_eq_log {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    (∫ y : ℝ, Set.indicator (Set.Ioc a c) (fun y : ℝ => y⁻¹) y) =
      Real.log c - Real.log a := by
  have hc : 0 < c := ha.trans_le hac
  calc
    (∫ y : ℝ, Set.indicator (Set.Ioc a c) (fun y : ℝ => y⁻¹) y) =
        ∫ y in Set.Ioc a c, y⁻¹ := integral_indicator measurableSet_Ioc
    _ = ∫ y : ℝ in a..c, y⁻¹ := (intervalIntegral.integral_of_le hac).symm
    _ = Real.log (c / a) := by simpa using (integral_inv_of_pos ha hc)
    _ = Real.log c - Real.log a := by rw [Real.log_div hc.ne' ha.ne']

theorem integral_rectangle_inverse_factorization {k : ℕ}
    (a c : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hac : ∀ i, a i ≤ c i) :
    (∫ t : Fin k → ℝ,
      ∏ i, Set.indicator (Set.Ioc (a i) (c i)) (fun y : ℝ => y⁻¹) (t i)) =
        ∏ i, (Real.log (c i) - Real.log (a i)) := by
  classical
  let g : Fin k → ℝ → ℝ := fun i y => Set.indicator (Set.Ioc (a i) (c i))
    (fun y : ℝ => y⁻¹) y
  calc
    _ = ∏ i, ∫ y : ℝ, g i y :=
      MeasureTheory.integral_fintype_prod_volume_eq_prod g
    _ = ∏ i, (Real.log (c i) - Real.log (a i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact integral_Ioc_inv_eq_log (ha i) (hac i)

lemma reciprocalIntervalIndicator_integrable {a c : ℝ}
    (ha : 0 < a) :
    Integrable (Set.indicator (Set.Ioc a c) (fun y : ℝ => y⁻¹)) volume := by
  have hcont : ContinuousOn (fun y : ℝ => y⁻¹) (Set.Icc a c) := by
    apply continuousOn_id.inv₀
    intro y hy
    exact ne_of_gt (ha.trans_le hy.1)
  have hIoc : IntegrableOn (fun y : ℝ => y⁻¹) (Set.Ioc a c) volume :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  exact hIoc.integrable_indicator measurableSet_Ioc

lemma reciprocalRectangleIntegrable {k : ℕ}
    (a c : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    Integrable (fun t : Fin k → ℝ =>
      ∏ i, Set.indicator (Set.Ioc (a i) (c i)) (fun y : ℝ => y⁻¹) (t i)) volume := by
  simpa only [volume_pi] using (Integrable.fintype_prod
    (fun i : Fin k => reciprocalIntervalIndicator_integrable (ha i)))

def simplexGridLower {k N : ℕ} (b h : ℝ) (j : Fin k → Fin N)
    (i : Fin k) : ℝ := b + ((j i).val : ℝ) * h

def simplexGridUpper {k N : ℕ} (b h : ℝ) (j : Fin k → Fin N)
    (i : Fin k) : ℝ := simplexGridLower b h j i + h

def simplexGridBox {k N : ℕ} (b h : ℝ) (j : Fin k → Fin N) :
    Set (Fin k → ℝ) :=
  {t | ∀ i, t i ∈ Set.Ioc (simplexGridLower b h j i) (simplexGridUpper b h j i)}

def simplexGridBoxInv {k N : ℕ} (b h : ℝ) (j : Fin k → Fin N)
    (t : Fin k → ℝ) : ℝ :=
  ∏ i, Set.indicator (Set.Ioc (simplexGridLower b h j i) (simplexGridUpper b h j i))
    (fun y : ℝ => y⁻¹) (t i)

def simplexGridInterior {k N : ℕ} (gamma w b h : ℝ)
    (j : Fin k → Fin N) : Prop :=
  (∀ i, gamma ≤ simplexGridLower b h j i) ∧
    (∑ i, simplexGridUpper b h j i) ≤ w - gamma

def simplexGridLowKernel {k N : ℕ} (w b h : ℝ)
    (j : Fin k → Fin N) : ℝ :=
  (w - ∑ i, simplexGridLower b h j i)⁻¹

def simplexGridCellMass (x b h : ℝ) (P : Finset ℕ) (j : ℕ) : ℝ :=
  primeLabelReciprocalIntervalMass x (b + (j : ℝ) * h)
    (b + ((j + 1 : ℕ) : ℝ) * h) P

def simplexGridCellLogWidth (b h : ℝ) (j : ℕ) : ℝ :=
  Real.log (b + ((j + 1 : ℕ) : ℝ) * h) - Real.log (b + (j : ℝ) * h)

lemma simplexGridCellLogWidth_eq_box {k N : ℕ} (b h : ℝ)
    (j : Fin k → Fin N) (i : Fin k) :
    simplexGridCellLogWidth b h (j i).val =
      Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i) := by
  simp only [simplexGridCellLogWidth, simplexGridUpper, simplexGridLower,
    Nat.cast_add, Nat.cast_one]
  congr 1 <;> ring_nf

theorem simplexGridBoxPrimeTupleMass_eq {k N : ℕ}
    (x b h : ℝ) (P : Finset ℕ) (j : Fin k → Fin N) :
    (∏ i, simplexGridCellMass x b h P (j i).val) =
      ∑ f : Fin k → PrimeLabel P,
        ∏ i, if (f i).val ∈
            (Finset.Ioc ⌊x ^ (simplexGridLower b h j i)⌋₊
              ⌊x ^ (simplexGridUpper b h j i)⌋₊).filter Nat.Prime then
          1 / ((f i).val : ℝ) else 0 := by
  calc
    (∏ i, simplexGridCellMass x b h P (j i).val) =
        ∏ i, primeLabelReciprocalIntervalMass x
          (b + ((j i).val : ℝ) * h) (b + ((j i).val : ℝ) * h + h) P := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [simplexGridCellMass]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := (primeLabelTupleRectangleMass_eq x
      (fun i : Fin k => b + ((j i).val : ℝ) * h)
      (fun i : Fin k => b + ((j i).val : ℝ) * h + h) (P := P)).symm

theorem simplexGridCellMass_uniform_log_upper {b h eps : ℝ}
    (hb : 0 < b) (hh : 0 ≤ h) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ, ∀ j : ℕ,
      simplexGridCellMass x b h P j ≤ simplexGridCellLogWidth b h j + eps := by
  filter_upwards [primeLabelReciprocalIntervalMass_uniform_log_upper hb heps] with x hx
  intro P j
  have hleft : b ≤ b + (j : ℝ) * h := by
    have hj : 0 ≤ (j : ℝ) := by positivity
    linarith [mul_nonneg hj hh]
  have hright : b + (j : ℝ) * h ≤ b + ((j + 1 : ℕ) : ℝ) * h := by
    have hj : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
    nlinarith [mul_nonneg (sub_nonneg.mpr hj) hh]
  exact hx P (b + (j : ℝ) * h) (b + ((j + 1 : ℕ) : ℝ) * h) hleft hright

theorem simplexGridCellLogWidth_bounds {b h W : ℝ} (hb : 0 < b)
    (hh : 0 < h) (j : ℕ) (hupper : b + ((j + 1 : ℕ) : ℝ) * h ≤ W) :
    h / W ≤ simplexGridCellLogWidth b h j ∧
      simplexGridCellLogWidth b h j ≤ h / b := by
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_num
  let a : ℝ := b + (j : ℝ) * h
  let c : ℝ := b + ((j + 1 : ℕ) : ℝ) * h
  have ha : 0 < a := by
    dsimp [a]
    have hj : 0 ≤ (j : ℝ) := by positivity
    linarith [mul_nonneg hj hh.le]
  have hac : a ≤ c := by
    dsimp [a, c]
    rw [hcast]
    nlinarith [mul_nonneg (by positivity : 0 ≤ (j : ℝ)) hh.le]
  have hcU : c ≤ W := hupper
  have hba : b ≤ a := by
    dsimp [a]
    have hj : 0 ≤ (j : ℝ) := by positivity
    linarith [mul_nonneg hj hh.le]
  have hwidth : c - a = h := by
    dsimp [a, c]
    rw [hcast]
    ring
  have hlower := log_interval_ge_length_div_upper ha hac hcU
  have hupperLog := log_interval_le_length_div hb hba hac
  rw [hwidth] at hlower hupperLog
  constructor
  · simpa [simplexGridCellLogWidth, a, c, hwidth] using hlower
  · simpa [simplexGridCellLogWidth, a, c, hwidth] using hupperLog

theorem simplexGridCellMass_sum_le {b h eps : ℝ} {N : ℕ}
    (hb : 0 < b) (hh : 0 ≤ h) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ,
      (∑ j : Fin N, simplexGridCellMass x b h P j.val) ≤
        (∑ j : Fin N, simplexGridCellLogWidth b h j.val) + (N : ℝ) * eps := by
  filter_upwards [simplexGridCellMass_uniform_log_upper hb hh heps] with x hx
  intro P
  calc
    (∑ j : Fin N, simplexGridCellMass x b h P j.val) ≤
        ∑ j : Fin N, (simplexGridCellLogWidth b h j.val + eps) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hx P j.val
    _ = (∑ j : Fin N, simplexGridCellLogWidth b h j.val) + (N : ℝ) * eps := by
          simp [Finset.sum_add_distrib]

theorem simplexGridBoxMassSum_eq {b h x : ℝ} {P : Finset ℕ}
    {k N : ℕ} :
    (∑ j : (Fin k → Fin N), ∏ i, simplexGridCellMass x b h P (j i).val) =
      (∑ j : Fin N, simplexGridCellMass x b h P j.val) ^ k := by
  classical
  exact (Fintype.sum_pow (fun j : Fin N => simplexGridCellMass x b h P j.val) k).symm

theorem simplexGridBoxLogWidthSum_eq {b h : ℝ} {k N : ℕ} :
    (∑ j : (Fin k → Fin N), ∏ i, simplexGridCellLogWidth b h (j i).val) =
      (∑ j : Fin N, simplexGridCellLogWidth b h j.val) ^ k := by
  classical
  exact (Fintype.sum_pow (fun j : Fin N => simplexGridCellLogWidth b h j.val) k).symm

theorem simplexGridBoxPrimeMassSum_le {x b h tau D : ℝ} {P : Finset ℕ}
    {k N : ℕ} (hD : 0 ≤ D) (htau : 0 ≤ tau)
    (hcell : (∑ j : Fin N, simplexGridCellMass x b h P j.val) ≤ D + (N : ℝ) * tau) :
    (∑ j : (Fin k → Fin N), ∏ i, simplexGridCellMass x b h P (j i).val) ≤
      D ^ k + (k : ℝ) * ((N : ℝ) * tau) * (1 + D + (N : ℝ) * tau) ^ k := by
  have hMnonneg : 0 ≤ ∑ j : Fin N, simplexGridCellMass x b h P j.val := by
    apply Finset.sum_nonneg
    intro j hj
    exact primeLabelReciprocalIntervalMass_nonneg x _ _ P
  have hE : 0 ≤ (N : ℝ) * tau := mul_nonneg (Nat.cast_nonneg N) htau
  have hMpow := pow_le_pow_left₀ hMnonneg hcell k
  have hdiff := pow_add_diff_le hD hE k
  calc
    (∑ j : (Fin k → Fin N), ∏ i, simplexGridCellMass x b h P (j i).val) =
        (∑ j : Fin N, simplexGridCellMass x b h P j.val) ^ k :=
          simplexGridBoxMassSum_eq
    _ ≤ (D + (N : ℝ) * tau) ^ k := hMpow
    _ ≤ D ^ k + (k : ℝ) * ((N : ℝ) * tau) *
          (1 + D + (N : ℝ) * tau) ^ k := by linarith [hdiff]

theorem simplexGridBox_mem_simplex {l N : ℕ} {gamma w b h : ℝ}
    {j : Fin (l - 1) → Fin N} {t : Fin (l - 1) → ℝ}
    (hJ : simplexGridInterior gamma w b h j)
    (ht : t ∈ simplexGridBox b h j) :
    (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma := by
  have ht' : ∀ i : Fin (l - 1),
      t i ∈ Set.Ioc (simplexGridLower b h j i) (simplexGridUpper b h j i) := by
    simpa [simplexGridBox] using ht
  constructor
  · intro i
    exact (hJ.1 i).trans (Set.mem_Ioc.mp (ht' i)).1.le
  · calc
      (∑ i, t i) ≤ ∑ i, simplexGridUpper b h j i :=
        Finset.sum_le_sum fun i hi => (Set.mem_Ioc.mp (ht' i)).2
      _ ≤ w - gamma := hJ.2

lemma simplexGridBoxInv_eq_prod_of_mem {k N : ℕ} {b h : ℝ}
    {j : Fin k → Fin N} {t : Fin k → ℝ} (ht : t ∈ simplexGridBox b h j) :
    simplexGridBoxInv b h j t = ∏ i, (t i)⁻¹ := by
  classical
  have hmem : ∀ i : Fin k,
      t i ∈ Set.Ioc (simplexGridLower b h j i) (simplexGridUpper b h j i) := by
    simpa [simplexGridBox] using ht
  simp [simplexGridBoxInv, hmem]

lemma simplexGridBoxInv_eq_zero_of_not_mem {k N : ℕ} {b h : ℝ}
    {j : Fin k → Fin N} {t : Fin k → ℝ} (ht : t ∉ simplexGridBox b h j) :
    simplexGridBoxInv b h j t = 0 := by
  classical
  have hnot : ¬ ∀ i : Fin k,
      t i ∈ Set.Ioc (simplexGridLower b h j i) (simplexGridUpper b h j i) := by
    simpa [simplexGridBox] using ht
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  unfold simplexGridBoxInv
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact Set.indicator_of_notMem hi (fun y : ℝ => y⁻¹)

theorem simplexGridLowKernel_le_simplexIntegrand {l N : ℕ}
    {gamma w b h : ℝ} (hgamma : 0 < gamma) (hh : 0 ≤ h)
    {j : Fin (l - 1) → Fin N} (hJ : simplexGridInterior gamma w b h j)
    {t : Fin (l - 1) → ℝ} (ht : t ∈ simplexGridBox b h j) :
    simplexGridLowKernel w b h j * simplexGridBoxInv b h j t ≤
      simplexDensityIntegrand gamma w l t := by
  have hsimplex := simplexGridBox_mem_simplex hJ ht
  have ht' : ∀ i : Fin (l - 1),
      t i ∈ Set.Ioc (simplexGridLower b h j i) (simplexGridUpper b h j i) := by
    simpa [simplexGridBox] using ht
  have hsumLower :
      (∑ i, simplexGridLower b h j i) ≤ ∑ i, simplexGridUpper b h j i :=
    Finset.sum_le_sum fun i hi => le_add_of_nonneg_right hh
  have hlowDen : gamma ≤ w - ∑ i, simplexGridLower b h j i := by
    linarith [hJ.1, hsumLower, hJ.2]
  have htDen : gamma ≤ w - ∑ i, t i := by linarith [hsimplex.2]
  have hkernel :
      (w - ∑ i, simplexGridLower b h j i)⁻¹ ≤ (w - ∑ i, t i)⁻¹ := by
    have hsum : (∑ i, simplexGridLower b h j i) ≤ ∑ i, t i :=
      Finset.sum_le_sum fun i hi => (Set.mem_Ioc.mp (ht' i)).1.le
    have hdenorder : (w - ∑ i, t i) ≤ w - ∑ i, simplexGridLower b h j i := by linarith
    simpa [one_div] using
      (one_div_le_one_div_of_le (by linarith [hsimplex.2] : 0 < w - ∑ i, t i) hdenorder)
  have hprod_nonneg : 0 ≤ ∏ i, (t i)⁻¹ :=
    Finset.prod_nonneg fun i hi => inv_nonneg.mpr (le_of_lt (hgamma.trans_le (hsimplex.1 i)))
  rw [simplexGridLowKernel]
  rw [simplexGridBoxInv_eq_prod_of_mem ht]
  have hF : simplexDensityIntegrand gamma w l t =
      (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ := by
    simp [simplexDensityIntegrand, hsimplex]
  calc
    (w - ∑ i, simplexGridLower b h j i)⁻¹ * ∏ i, (t i)⁻¹ ≤
      (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ :=
        mul_le_mul_of_nonneg_right hkernel hprod_nonneg
    _ = simplexDensityIntegrand gamma w l t := hF.symm

lemma simplexDensityIntegrand_nonneg {gamma w : ℝ} {l : ℕ}
    (hgamma : 0 < gamma) (t : Fin (l - 1) → ℝ) :
    0 ≤ simplexDensityIntegrand gamma w l t := by
  unfold simplexDensityIntegrand
  split_ifs with h
  · rcases h with ⟨ht, hsum⟩
    have hden : 0 < w - ∑ i, t i := by linarith
    have hprod : 0 ≤ ∏ i, (t i)⁻¹ :=
      Finset.prod_nonneg fun i hi => inv_nonneg.mpr (le_of_lt (hgamma.trans_le (ht i)))
    exact mul_nonneg (inv_nonneg.mpr hden.le) hprod
  · simp

theorem simplexGridInterior_sum_pointwise {l N : ℕ} {gamma w b h : ℝ}
    (hgamma : 0 < gamma) (hh : 0 ≤ h)
    (J : Finset (Fin (l - 1) → Fin N))
    (hJ : ∀ j ∈ J, simplexGridInterior gamma w b h j)
    (hpair : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' →
      Disjoint (simplexGridBox b h j) (simplexGridBox b h j')) :
    ∀ t : Fin (l - 1) → ℝ,
      (∑ j ∈ J, simplexGridLowKernel w b h j * simplexGridBoxInv b h j t) ≤
        simplexDensityIntegrand gamma w l t := by
  intro t
  by_cases hbox : ∃ j ∈ J, t ∈ simplexGridBox b h j
  · obtain ⟨j, hj, htj⟩ := hbox
    have hsum : (∑ j' ∈ J,
        simplexGridLowKernel w b h j' * simplexGridBoxInv b h j' t) =
          simplexGridLowKernel w b h j * simplexGridBoxInv b h j t := by
      apply Finset.sum_eq_single j
      · intro j' hj' hne
        have hdis := Set.disjoint_left.mp (hpair j hj j' hj' hne.symm)
        have hnot : t ∉ simplexGridBox b h j' := by
          intro ht'
          exact hdis htj ht'
        simp [simplexGridBoxInv_eq_zero_of_not_mem hnot]
      · intro hnot
        exact False.elim (hnot hj)
    rw [hsum]
    exact simplexGridLowKernel_le_simplexIntegrand hgamma hh (hJ j hj) htj
  · have hzero :
        (∑ j ∈ J, simplexGridLowKernel w b h j * simplexGridBoxInv b h j t) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hnot : t ∉ simplexGridBox b h j := by
        intro htj
        exact hbox ⟨j, hj, htj⟩
      simp [simplexGridBoxInv_eq_zero_of_not_mem hnot]
    rw [hzero]
    exact simplexDensityIntegrand_nonneg hgamma t

lemma simplexGridBoxInv_integrable {k N : ℕ} {b h : ℝ}
    (hb : 0 < b) (hh : 0 ≤ h) (j : Fin k → Fin N) :
    Integrable (simplexGridBoxInv b h j) volume := by
  unfold simplexGridBoxInv
  apply reciprocalRectangleIntegrable
  intro i
  have hj : 0 ≤ ((j i).val : ℝ) := by positivity
  dsimp [simplexGridLower]
  linarith [mul_nonneg hj hh]

lemma simplexGridBoxInv_integral {k N : ℕ} {b h : ℝ}
    (hb : 0 < b) (hh : 0 ≤ h) (j : Fin k → Fin N) :
    (∫ t : Fin k → ℝ, simplexGridBoxInv b h j t) =
      ∏ i : Fin k, (Real.log (simplexGridUpper b h j i) -
        Real.log (simplexGridLower b h j i)) := by
  unfold simplexGridBoxInv
  apply integral_rectangle_inverse_factorization
  · intro i
    have hj : 0 ≤ ((j i).val : ℝ) := by positivity
    have hlow : 0 < b + ((j i).val : ℝ) * h := by
      have := mul_nonneg hj hh
      linarith
    simpa [simplexGridLower] using hlow
  · intro i
    exact le_add_of_nonneg_right hh

lemma simplexGridBoxInv_const_integral {k N : ℕ} {b h C : ℝ}
    (hb : 0 < b) (hh : 0 ≤ h) (j : Fin k → Fin N) :
    (∫ t : Fin k → ℝ, C * simplexGridBoxInv b h j t) =
      C * ∏ i : Fin k,
        (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := by
  rw [MeasureTheory.integral_const_mul, simplexGridBoxInv_integral hb hh j]

theorem simplexGridInterior_lowSum_le_densityTerm {l N : ℕ}
    {gamma w b h : ℝ} (hl : 2 ≤ l) (hgamma : 0 < gamma) (hw : gamma < w)
    (hb : 0 < b) (hh : 0 ≤ h)
    (J : Finset (Fin (l - 1) → Fin N))
    (hJ : ∀ j ∈ J, simplexGridInterior gamma w b h j)
    (hpair : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' →
      Disjoint (simplexGridBox b h j) (simplexGridBox b h j')) :
    (∑ j ∈ J, simplexGridLowKernel w b h j *
      ∏ i : Fin (l - 1),
        (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i))) ≤
      densityTerm gamma w l := by
  have hterms : ∀ j ∈ J, Integrable
      (fun t : Fin (l - 1) → ℝ =>
        simplexGridLowKernel w b h j * simplexGridBoxInv b h j t) volume := by
    intro j hj
    exact (simplexGridBoxInv_integrable hb hh j).const_mul (simplexGridLowKernel w b h j)
  have hsumInt := integrable_finsetSum J hterms
  have hFint := simplexDensityIntegrand_integrable hl hgamma hw
  have hpoint := simplexGridInterior_sum_pointwise hgamma hh J hJ hpair
  calc
    _ = ∑ j ∈ J, ∫ t : Fin (l - 1) → ℝ,
          simplexGridLowKernel w b h j * simplexGridBoxInv b h j t := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (simplexGridBoxInv_const_integral
          (C := simplexGridLowKernel w b h j) hb hh j).symm
    _ = ∫ t : Fin (l - 1) → ℝ,
          ∑ j ∈ J, simplexGridLowKernel w b h j * simplexGridBoxInv b h j t :=
        (integral_finsetSum J hterms).symm
    _ ≤ ∫ t : Fin (l - 1) → ℝ, simplexDensityIntegrand gamma w l t :=
        integral_mono hsumInt hFint hpoint
    _ = densityTerm gamma w l := (densityTerm_integrand_eq_integral gamma w l).symm

theorem simplexGridHighKernel_le_low_add_variation {l N : ℕ}
    {gamma w b h : ℝ} (hgamma : 0 < gamma) (hh : 0 ≤ h)
    {j : Fin (l - 1) → Fin N} (hJ : simplexGridInterior gamma w b h j) :
    (w - ∑ i, simplexGridUpper b h j i)⁻¹ ≤
      simplexGridLowKernel w b h j + ((l - 1 : ℕ) : ℝ) * h / gamma ^ 2 := by
  have hsumDiff :
      (∑ i : Fin (l - 1), simplexGridUpper b h j i) -
        (∑ i : Fin (l - 1), simplexGridLower b h j i) =
          ((l - 1 : ℕ) : ℝ) * h := by
    calc
      _ = (∑ i : Fin (l - 1), (simplexGridLower b h j i + h)) -
          ∑ i : Fin (l - 1), simplexGridLower b h j i := by simp [simplexGridUpper]
      _ = (∑ i : Fin (l - 1), simplexGridLower b h j i +
          ∑ _i : Fin (l - 1), h) - ∑ i, simplexGridLower b h j i := by
            rw [Finset.sum_add_distrib]
      _ = ((l - 1 : ℕ) : ℝ) * h := by simp
  have hsumLowerUpper :
      (∑ i, simplexGridLower b h j i) ≤ ∑ i, simplexGridUpper b h j i :=
    Finset.sum_le_sum fun i hi => le_add_of_nonneg_right hh
  have hupperDen : gamma ≤ w - ∑ i, simplexGridUpper b h j i := by linarith [hJ.2]
  have hlowerDen : gamma ≤ w - ∑ i, simplexGridLower b h j i := by
    linarith [hJ.2, hsumLowerUpper]
  have hupperPos : 0 < w - ∑ i, simplexGridUpper b h j i := hgamma.trans_le hupperDen
  have hlowerPos : 0 < w - ∑ i, simplexGridLower b h j i := hgamma.trans_le hlowerDen
  have hidentity :
      (w - ∑ i, simplexGridUpper b h j i)⁻¹ =
        (w - ∑ i, simplexGridLower b h j i)⁻¹ +
          ((∑ i, simplexGridUpper b h j i) -
            (∑ i, simplexGridLower b h j i)) /
              ((w - ∑ i, simplexGridUpper b h j i) *
                (w - ∑ i, simplexGridLower b h j i)) := by
    field_simp [ne_of_gt hupperPos, ne_of_gt hlowerPos]
    ring
  have hnum : 0 ≤ ((l - 1 : ℕ) : ℝ) * h := mul_nonneg (by positivity) hh
  have hprod : gamma ^ 2 ≤
      (w - ∑ i, simplexGridUpper b h j i) *
        (w - ∑ i, simplexGridLower b h j i) := by nlinarith [hupperDen, hlowerDen]
  calc
    (w - ∑ i, simplexGridUpper b h j i)⁻¹ =
        (w - ∑ i, simplexGridLower b h j i)⁻¹ +
          ((∑ i, simplexGridUpper b h j i) -
            (∑ i, simplexGridLower b h j i)) /
              ((w - ∑ i, simplexGridUpper b h j i) *
                (w - ∑ i, simplexGridLower b h j i)) := hidentity
    _ ≤ simplexGridLowKernel w b h j + ((l - 1 : ℕ) : ℝ) * h / gamma ^ 2 := by
      dsimp [simplexGridLowKernel]
      have hfrac :
          ((∑ i, simplexGridUpper b h j i) -
            (∑ i, simplexGridLower b h j i)) /
              ((w - ∑ i, simplexGridUpper b h j i) *
                (w - ∑ i, simplexGridLower b h j i)) ≤
            ((l - 1 : ℕ) : ℝ) * h / gamma ^ 2 := by
        apply (div_le_div_iff₀ (mul_pos hupperPos hlowerPos) (sq_pos_of_pos hgamma)).2
        rw [hsumDiff]
        nlinarith [hnum, hprod]
      linarith [hfrac]

theorem simplexGridInterior_highSum_le_densityTerm {l N : ℕ}
    {gamma w b h : ℝ} (hl : 2 ≤ l) (hgamma : 0 < gamma) (hw : gamma < w)
    (hb : 0 < b) (hh : 0 ≤ h)
    (J : Finset (Fin (l - 1) → Fin N))
    (hJ : ∀ j ∈ J, simplexGridInterior gamma w b h j)
    (hpair : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' →
      Disjoint (simplexGridBox b h j) (simplexGridBox b h j')) :
    (∑ j ∈ J, (w - ∑ i, simplexGridUpper b h j i)⁻¹ *
      ∏ i : Fin (l - 1),
        (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i))) ≤
      densityTerm gamma w l + (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
        ∑ j ∈ J, ∏ i : Fin (l - 1),
          (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := by
  have hvar : 0 ≤ ((l - 1 : ℕ) : ℝ) * h / gamma ^ 2 := by positivity
  have hvol_nonneg (j : Fin (l - 1) → Fin N) (hj : j ∈ J) :
      0 ≤ ∏ i : Fin (l - 1),
        (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := by
    apply Finset.prod_nonneg
    intro i hi
    have hlow : 0 < simplexGridLower b h j i := by
      have hji := hJ j hj
      linarith [hji.1 i]
    have hupper : simplexGridLower b h j i ≤ simplexGridUpper b h j i :=
      le_add_of_nonneg_right hh
    exact sub_nonneg.mpr (Real.log_le_log hlow hupper)
  calc
    _ ≤ ∑ j ∈ J,
        (simplexGridLowKernel w b h j + ((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
          ∏ i : Fin (l - 1),
            (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (simplexGridHighKernel_le_low_add_variation hgamma hh (hJ j hj))
        (hvol_nonneg j hj)
    _ = ∑ j ∈ J,
        (simplexGridLowKernel w b h j + ((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
          ∏ i : Fin (l - 1),
            (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j ∈ J, (simplexGridLowKernel w b h j *
          ∏ i : Fin (l - 1),
            (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) +
          (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
            ∏ i : Fin (l - 1),
              (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i))) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j ∈ J, simplexGridLowKernel w b h j *
          ∏ i : Fin (l - 1),
            (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i))) +
        (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
          ∑ j ∈ J, ∏ i : Fin (l - 1),
            (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ densityTerm gamma w l + (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
          ∑ j ∈ J, ∏ i : Fin (l - 1),
            (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := by
      have hlow := simplexGridInterior_lowSum_le_densityTerm hl hgamma hw hb hh J hJ hpair
      linarith

theorem finProd_le_of_nonneg {k : ℕ} (a b : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) (hb : ∀ i, 0 ≤ b i) :
    (∏ i, a i) ≤ ∏ i, b i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      apply mul_le_mul (hab 0) ?_ ?_ (hb 0)
      · exact ih (fun i => a i.succ) (fun i => b i.succ)
          (fun i => ha i.succ) (fun i => hab i.succ) (fun i => hb i.succ)
      · exact Finset.prod_nonneg fun i hi => ha i.succ

theorem simplexGridInterior_primeMass_le {x gamma w b h tau D : ℝ}
    {P : Finset ℕ} {l N : ℕ}
    (hl : 2 ≤ l) (hgamma : 0 < gamma) (hw : gamma < w)
    (hb : 0 < b) (hbg : b ≤ gamma) (hh : 0 ≤ h)
    (htau : 0 ≤ tau)
    (hDsum : (∑ j : Fin N, simplexGridCellLogWidth b h j.val) = D)
    (hmass : ∀ j : Fin N,
      simplexGridCellMass x b h P j.val ≤ simplexGridCellLogWidth b h j.val + tau)
    (J : Finset (Fin (l - 1) → Fin N))
    (hJ : ∀ j ∈ J, simplexGridInterior gamma w b h j)
    (hpair : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' →
      Disjoint (simplexGridBox b h j) (simplexGridBox b h j')) :
    (∑ v ∈ J, (w - ∑ i, simplexGridUpper b h v i)⁻¹ *
      ∏ i : Fin (l - 1), simplexGridCellMass x b h P (v i).val) ≤
      densityTerm gamma w l + (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) * D ^ (l - 1) +
        b⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1)) := by
  let d : Fin N → ℝ := fun j => simplexGridCellLogWidth b h j.val
  let m : Fin N → ℝ := fun j => simplexGridCellMass x b h P j.val
  let vol : (Fin (l - 1) → Fin N) → ℝ := fun v => ∏ i, d (v i)
  let mass : (Fin (l - 1) → Fin N) → ℝ := fun v => ∏ i, m (v i)
  let upperVol : (Fin (l - 1) → Fin N) → ℝ := fun v => ∏ i, (d (v i) + tau)
  have hd_nonneg (j : Fin N) : 0 ≤ d j := by
    dsimp [d, simplexGridCellLogWidth]
    have ha : 0 < b + (j.val : ℝ) * h := by
      have hj : 0 ≤ (j.val : ℝ) := by positivity
      linarith [mul_nonneg hj hh]
    have hc : b + (j.val : ℝ) * h ≤ b + ((j.val + 1 : ℕ) : ℝ) * h := by
      have hj : (j.val : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j.val
      nlinarith [mul_nonneg (sub_nonneg.mpr hj) hh]
    exact sub_nonneg.mpr (Real.log_le_log ha hc)
  have hm_nonneg (j : Fin N) : 0 ≤ m j := by
    dsimp [m]
    exact primeLabelReciprocalIntervalMass_nonneg x _ _ P
  have hvol_nonneg (v : Fin (l - 1) → Fin N) : 0 ≤ vol v := by
    dsimp [vol]
    exact Finset.prod_nonneg fun i hi => hd_nonneg (v i)
  have hmass_nonneg (v : Fin (l - 1) → Fin N) : 0 ≤ mass v := by
    dsimp [mass]
    exact Finset.prod_nonneg fun i hi => hm_nonneg (v i)
  have hmass_le_upperVol (v : Fin (l - 1) → Fin N) : mass v ≤ upperVol v := by
    dsimp [mass, upperVol]
    apply finProd_le_of_nonneg
    · intro i
      exact hm_nonneg (v i)
    · intro i
      exact hmass (v i)
    · intro i
      exact add_nonneg (hd_nonneg (v i)) htau
  have hvol_le_upperVol (v : Fin (l - 1) → Fin N) : vol v ≤ upperVol v := by
    dsimp [vol, upperVol]
    apply finProd_le_of_nonneg
    · intro i
      exact hd_nonneg (v i)
    · intro i
      exact le_add_of_nonneg_right htau
    · intro i
      exact add_nonneg (hd_nonneg (v i)) htau
  have hhigh_le (v : Fin (l - 1) → Fin N) (hv : v ∈ J) :
      0 ≤ (w - ∑ i, simplexGridUpper b h v i)⁻¹ ∧
      (w - ∑ i, simplexGridUpper b h v i)⁻¹ ≤ b⁻¹ := by
    have hden : gamma ≤ w - ∑ i, simplexGridUpper b h v i := by
      linarith [(hJ v hv).2]
    have hpos : 0 < w - ∑ i, simplexGridUpper b h v i := hgamma.trans_le hden
    have hfirst : (w - ∑ i, simplexGridUpper b h v i)⁻¹ ≤ gamma⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hgamma hden
    have hsecond : gamma⁻¹ ≤ b⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hb hbg
    exact ⟨inv_nonneg.mpr hpos.le, hfirst.trans hsecond⟩
  have hterm (v : Fin (l - 1) → Fin N) (hv : v ∈ J) :
      (w - ∑ i, simplexGridUpper b h v i)⁻¹ * mass v ≤
        (w - ∑ i, simplexGridUpper b h v i)⁻¹ * vol v +
          b⁻¹ * (upperVol v - vol v) := by
    obtain ⟨hhighNonneg, hhighBound⟩ := hhigh_le v hv
    have hdelta : 0 ≤ upperVol v - vol v := sub_nonneg.mpr (hvol_le_upperVol v)
    have hmul := mul_le_mul_of_nonneg_left (hmass_le_upperVol v) hhighNonneg
    have herr := mul_le_mul_of_nonneg_right hhighBound hdelta
    calc
      (w - ∑ i, simplexGridUpper b h v i)⁻¹ * mass v ≤
          (w - ∑ i, simplexGridUpper b h v i)⁻¹ * upperVol v := hmul
      _ = (w - ∑ i, simplexGridUpper b h v i)⁻¹ * vol v +
            (w - ∑ i, simplexGridUpper b h v i)⁻¹ * (upperVol v - vol v) := by ring
      _ ≤ (w - ∑ i, simplexGridUpper b h v i)⁻¹ * vol v + b⁻¹ * (upperVol v - vol v) := by
        linarith [herr]
  have hDsum' : (∑ j : Fin N, d j) = D := by simpa [d] using hDsum
  have hMassSum : (∑ j : Fin N, m j) ≤ D + (N : ℝ) * tau := by
    calc
      (∑ j : Fin N, m j) ≤ ∑ j : Fin N, (d j + tau) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hmass j
      _ = D + (N : ℝ) * tau := by
        rw [Finset.sum_add_distrib, hDsum']
        simp
  have hvolSum : (∑ v : Fin (l - 1) → Fin N, vol v) = D ^ (l - 1) := by
    calc
      (∑ v : Fin (l - 1) → Fin N, vol v) =
          (∑ j : Fin N, d j) ^ (l - 1) := by
            dsimp [vol, d]
            exact simplexGridBoxLogWidthSum_eq
      _ = D ^ (l - 1) := by rw [hDsum']
  have hupperVolSum :
      (∑ v : Fin (l - 1) → Fin N, upperVol v) = (D + (N : ℝ) * tau) ^ (l - 1) := by
    have hcell : (∑ j : Fin N, (d j + tau)) = D + (N : ℝ) * tau := by
      rw [Finset.sum_add_distrib, hDsum']
      simp
    calc
      (∑ v : Fin (l - 1) → Fin N, upperVol v) =
          (∑ j : Fin N, (d j + tau)) ^ (l - 1) := by
            dsimp [upperVol]
            exact (Fintype.sum_pow (fun j : Fin N => d j + tau) (l - 1)).symm
      _ = (D + (N : ℝ) * tau) ^ (l - 1) := by rw [hcell]
  have herrorAll :
      (∑ v : Fin (l - 1) → Fin N, (upperVol v - vol v)) =
        (D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1) := by
    rw [Finset.sum_sub_distrib, hupperVolSum, hvolSum]
  have herrorJ : (∑ v ∈ J, (upperVol v - vol v)) ≤
      (D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1) := by
    calc
      (∑ v ∈ J, (upperVol v - vol v)) ≤
          ∑ v : Fin (l - 1) → Fin N, (upperVol v - vol v) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
            intro v hv hnot
            exact sub_nonneg.mpr (hvol_le_upperVol v)
      _ = _ := herrorAll
  have hhighVol := simplexGridInterior_highSum_le_densityTerm
    hl hgamma hw hb hh J hJ hpair
  have hhighVol' :
      (∑ v ∈ J, (w - ∑ i, simplexGridUpper b h v i)⁻¹ * vol v) ≤
        densityTerm gamma w l + (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
          ∑ j ∈ J, vol j := by
    have hvolEq (v : Fin (l - 1) → Fin N) : vol v =
        ∏ i : Fin (l - 1),
          (Real.log (simplexGridUpper b h v i) - Real.log (simplexGridLower b h v i)) := by
      dsimp [vol, d]
      apply Finset.prod_congr rfl
      intro i hi
      exact simplexGridCellLogWidth_eq_box b h v i
    have hsumEq :
        (∑ j ∈ J, ∏ i : Fin (l - 1),
          (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i))) =
          ∑ j ∈ J, vol j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hvolEq j).symm
    calc
      _ = ∑ j ∈ J, (w - ∑ i, simplexGridUpper b h j i)⁻¹ *
          ∏ i : Fin (l - 1),
            (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hvolEq j]
      _ ≤ densityTerm gamma w l + (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
          ∑ j ∈ J, ∏ i : Fin (l - 1),
            (Real.log (simplexGridUpper b h j i) - Real.log (simplexGridLower b h j i)) := hhighVol
      _ = _ := by rw [hsumEq]
  have hvolJ : (∑ v ∈ J, vol v) ≤ D ^ (l - 1) := by
    calc
      (∑ v ∈ J, vol v) ≤ ∑ v : Fin (l - 1) → Fin N, vol v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
        intro v hv hnot
        exact hvol_nonneg v
      _ = D ^ (l - 1) := hvolSum
  have hvar : 0 ≤ ((l - 1 : ℕ) : ℝ) * h / gamma ^ 2 := by positivity
  have hhighVolBound :
      (∑ v ∈ J, (w - ∑ i, simplexGridUpper b h v i)⁻¹ * vol v) ≤
        densityTerm gamma w l + (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) * D ^ (l - 1) := by
    calc
      _ ≤ densityTerm gamma w l + (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) *
            ∑ j ∈ J, vol j := hhighVol'
      _ ≤ _ := by
        have hmul := mul_le_mul_of_nonneg_left hvolJ hvar
        nlinarith
  calc
    (∑ v ∈ J, (w - ∑ i, simplexGridUpper b h v i)⁻¹ * mass v) ≤
        (∑ v ∈ J, (w - ∑ i, simplexGridUpper b h v i)⁻¹ * vol v) +
          b⁻¹ * (∑ v ∈ J, (upperVol v - vol v)) := by
      calc
        _ ≤ ∑ v ∈ J,
            ((w - ∑ i, simplexGridUpper b h v i)⁻¹ * vol v +
              b⁻¹ * (upperVol v - vol v)) :=
              Finset.sum_le_sum fun v hv => hterm v hv
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ densityTerm gamma w l + (((l - 1 : ℕ) : ℝ) * h / gamma ^ 2) * D ^ (l - 1) +
          b⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1)) := by
      have hErrDiv := mul_le_mul_of_nonneg_left herrorJ (inv_nonneg.mpr hb.le)
      simpa [add_assoc] using add_le_add hhighVolBound hErrDiv

lemma gridExponentUpper_le_of_index_lt {b h : ℝ} (hh : 0 ≤ h)
    {j j' : ℕ} (hjj : j < j') :
    b + (j : ℝ) * h + h ≤ b + (j' : ℝ) * h := by
  have hcast : (j : ℝ) + 1 ≤ (j' : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hjj)
  nlinarith [mul_nonneg (sub_nonneg.mpr hcast) hh]

lemma simplexGridBox_disjoint {k N : ℕ} {b h : ℝ}
    (hh : 0 ≤ h) {j j' : Fin k → Fin N} (hjj : j ≠ j') :
    Disjoint (simplexGridBox b h j) (simplexGridBox b h j') := by
  apply Set.disjoint_left.mpr
  intro t ht ht'
  have hcoord : ∃ i, j i ≠ j' i := by
    by_contra hn
    push_neg at hn
    apply hjj
    funext i
    exact hn i
  obtain ⟨i, hi⟩ := hcoord
  change (∀ q : Fin k, t q ∈ Set.Ioc (simplexGridLower b h j q) (simplexGridUpper b h j q)) at ht
  change (∀ q : Fin k, t q ∈ Set.Ioc (simplexGridLower b h j' q) (simplexGridUpper b h j' q)) at ht'
  have hmem := ht i
  have hmem' := ht' i
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · have horder : simplexGridUpper b h j i ≤ simplexGridLower b h j' i := by
      exact gridExponentUpper_le_of_index_lt (b := b) hh (by exact_mod_cast hlt)
    have hti := (Set.mem_Ioc.mp hmem)
    have hti' := (Set.mem_Ioc.mp hmem')
    linarith [hti.2, hti'.1]
  · have horder : simplexGridUpper b h j' i ≤ simplexGridLower b h j i := by
      exact gridExponentUpper_le_of_index_lt (b := b) hh (by exact_mod_cast hlt)
    have hti := (Set.mem_Ioc.mp hmem)
    have hti' := (Set.mem_Ioc.mp hmem')
    linarith [hti.1, hti'.2]

def tupleProduct {P : Finset ℕ} {l : ℕ} (f : Fin l → PrimeLabel P) : ℕ :=
  ∏ i, (f i).val

def squarefreeCellFinset (I P : Finset ℕ) (l : ℕ) : Finset ℕ :=
  I.filter fun n => Squarefree n ∧ n.primeFactors.card = l ∧ n.primeFactors ⊆ P

def primeTupleCellFinset (I P : Finset ℕ) (l : ℕ) : Finset (Fin l → PrimeLabel P) :=
  Finset.univ.filter fun f => tupleProduct f ∈ I

abbrev SquarefreeCellPoint (I P : Finset ℕ) (l : ℕ) :=
  {n : ℕ // n ∈ squarefreeCellFinset I P l}

noncomputable def squarefreeFactorEquiv {I P : Finset ℕ} {l : ℕ}
    (n : SquarefreeCellPoint I P l) : Fin l ≃ {p // p ∈ n.val.primeFactors} :=
  (n.val.primeFactors.equivFinOfCardEq
    ((Finset.mem_filter.mp n.property).2.2.1)).symm

noncomputable def squarefreeFactorTuple {I P : Finset ℕ} {l : ℕ}
    (n : SquarefreeCellPoint I P l) (i : Fin l) : PrimeLabel P :=
  let p := squarefreeFactorEquiv n i
  ⟨p.val, (Finset.mem_filter.mp n.property).2.2.2 p.property⟩

noncomputable def squarefreeTuplePerm {I P : Finset ℕ} {l : ℕ}
    (n : SquarefreeCellPoint I P l) (σ : Equiv.Perm (Fin l)) : Fin l → PrimeLabel P :=
  fun i => squarefreeFactorTuple n (σ i)

theorem squarefreeFactorTuple_product {I P : Finset ℕ} {l : ℕ}
    (n : SquarefreeCellPoint I P l) : tupleProduct (squarefreeFactorTuple n) = n.val := by
  have hsquarefree := (Finset.mem_filter.mp n.property).2.1
  have hprod := prod_equiv_finset n.val.primeFactors (fun p : ℕ => p)
    (squarefreeFactorEquiv n)
  simpa [tupleProduct, squarefreeFactorTuple, Nat.prod_primeFactors_of_squarefree hsquarefree]
    using hprod

theorem squarefreeTuplePerm_product {I P : Finset ℕ} {l : ℕ}
    (n : SquarefreeCellPoint I P l) (σ : Equiv.Perm (Fin l)) :
    tupleProduct (squarefreeTuplePerm n σ) = n.val := by
  have hperm : tupleProduct (squarefreeTuplePerm n σ) = tupleProduct (squarefreeFactorTuple n) := by
    unfold tupleProduct squarefreeTuplePerm
    exact Fintype.prod_equiv σ
      (fun i => (squarefreeFactorTuple n (σ i)).val)
      (fun i => (squarefreeFactorTuple n i).val)
      (fun _ => rfl)
  exact hperm.trans (squarefreeFactorTuple_product n)

noncomputable def squarefreeTupleMap {I P : Finset ℕ} {l : ℕ} :
    (Σ n : SquarefreeCellPoint I P l, Equiv.Perm (Fin l)) →
      {f : Fin l → PrimeLabel P // f ∈ primeTupleCellFinset I P l} := fun u =>
  ⟨squarefreeTuplePerm u.1 u.2, by
    rw [primeTupleCellFinset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [squarefreeTuplePerm_product]
    exact (Finset.mem_filter.mp u.1.property).1⟩

theorem squarefreeTupleMap_injective {I P : Finset ℕ} {l : ℕ} :
    Function.Injective (@squarefreeTupleMap I P l) := by
  intro u v huv
  rcases u with ⟨n, σ⟩
  rcases v with ⟨m, τ⟩
  simp only [squarefreeTupleMap, Subtype.mk.injEq] at huv
  have hprod := congrArg tupleProduct huv
  rw [squarefreeTuplePerm_product, squarefreeTuplePerm_product] at hprod
  have hnm : n.val = m.val := hprod
  have hpoint : n = m := Subtype.ext hnm
  subst m
  congr 1
  apply Equiv.ext
  intro i
  apply (squarefreeFactorEquiv n).injective
  have hi := congrArg Subtype.val (congrFun huv i)
  change (squarefreeFactorEquiv n (σ i)).val =
    (squarefreeFactorEquiv n (τ i)).val at hi
  exact Subtype.ext hi

theorem squarefreeCell_factorial_card_le (I P : Finset ℕ) (l : ℕ) :
    (squarefreeCellFinset I P l).card * l.factorial ≤
      (primeTupleCellFinset I P l).card := by
  let S := squarefreeCellFinset I P l
  let A := SquarefreeCellPoint I P l
  let T := primeTupleCellFinset I P l
  have hcardSigma : Fintype.card (Σ n : A, Equiv.Perm (Fin l)) = S.card * l.factorial := by
    rw [Fintype.card_sigma]
    simp [A, S, Fintype.card_perm]
  have hinj := Fintype.card_le_of_injective (@squarefreeTupleMap I P l)
    squarefreeTupleMap_injective
  have hcardT : Fintype.card {f : Fin l → PrimeLabel P // f ∈ T} = T.card := by
    exact Fintype.card_coe T
  calc
    S.card * l.factorial = Fintype.card (Σ n : A, Equiv.Perm (Fin l)) := hcardSigma.symm
    _ ≤ Fintype.card {f : Fin l → PrimeLabel P // f ∈ T} := hinj
    _ = T.card := hcardT

def tupleTailProduct {P : Finset ℕ} {k : ℕ} (f : Fin k → PrimeLabel P) : ℕ :=
  ∏ i, (f i).val

def primeLogCoordinate (x : ℝ) (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / Analytic.L x

lemma primeLogCoordinate_rpow {x : ℝ} (hx : 1 < x) {p : ℕ}
    (hp : Nat.Prime p) : x ^ primeLogCoordinate x p = (p : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  calc
    x ^ primeLogCoordinate x p =
        Real.exp (Real.log x * primeLogCoordinate x p) :=
          Real.rpow_def_of_pos hx0 _
    _ = Real.exp (Real.log (p : ℝ)) := by
          congr 1
          dsimp [primeLogCoordinate, Analytic.L]
          field_simp [ne_of_gt (Real.log_pos hx)]
    _ = (p : ℝ) := Real.exp_log hp0

lemma primeInterval_mem_logCoordinate {x a c : ℝ} {p : ℕ}
    (hx : 1 < x) (hp : Nat.Prime p)
    (hmem : p ∈ (Finset.Ioc ⌊x ^ a⌋₊ ⌊x ^ c⌋₊).filter Nat.Prime) :
    a < primeLogCoordinate x p ∧ primeLogCoordinate x p ≤ c := by
  have hx0 : 0 < x := by linarith
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hL : 0 < Analytic.L x := by
    simpa [Analytic.L] using Real.log_pos hx
  have hmem' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem).1
  have hnatSucc : ⌊x ^ a⌋₊ + 1 ≤ p := by omega
  have hcastSucc : ((⌊x ^ a⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hnatSucc
  rw [Nat.cast_add, Nat.cast_one] at hcastSucc
  have hfloorLow : x ^ a < (⌊x ^ a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hrealLow : x ^ a < (p : ℝ) := hfloorLow.trans_le hcastSucc
  have hcastHigh : (p : ℝ) ≤ (⌊x ^ c⌋₊ : ℝ) := by exact_mod_cast hmem'.2
  have hfloorHigh : (⌊x ^ c⌋₊ : ℝ) ≤ x ^ c := Nat.floor_le (by positivity)
  have hrealHigh : (p : ℝ) ≤ x ^ c := hcastHigh.trans hfloorHigh
  have hlogLow := Real.log_lt_log (Real.rpow_pos_of_pos hx0 a) hrealLow
  rw [Real.log_rpow hx0 a] at hlogLow
  have hcoordLow : a < primeLogCoordinate x p := by
    apply (lt_div_iff₀ hL).2
    simpa [primeLogCoordinate, Analytic.L, mul_comm] using hlogLow
  have hlogHigh := Real.log_le_log hp0 hrealHigh
  rw [Real.log_rpow hx0 c] at hlogHigh
  have hcoordHigh : primeLogCoordinate x p ≤ c := by
    apply (div_le_iff₀ hL).2
    simpa [primeLogCoordinate, Analytic.L, mul_comm] using hlogHigh
  exact ⟨hcoordLow, hcoordHigh⟩

lemma tupleTailProduct_inv_eq_prod_inv {P : Finset ℕ} {k : ℕ}
    (f : Fin k → PrimeLabel P) :
    (tupleTailProduct f : ℝ)⁻¹ = ∏ i, ((f i).val : ℝ)⁻¹ := by
  simp [tupleTailProduct, Nat.cast_prod, Finset.prod_inv_distrib]

lemma tupleTailProduct_eq_rpow_sum {P : Finset ℕ} {k : ℕ}
    {x : ℝ} (hx : 1 < x) (hP : ∀ p ∈ P, Nat.Prime p)
    (f : Fin k → PrimeLabel P) :
    (tupleTailProduct f : ℝ) = x ^ ∑ i, primeLogCoordinate x (f i).val := by
  have hx0 : 0 < x := by linarith
  have hcast : (tupleTailProduct f : ℝ) = ∏ i, ((f i).val : ℝ) := by
    simp [tupleTailProduct, Nat.cast_prod]
  have heach (i : Fin k) :
      x ^ primeLogCoordinate x (f i).val = ((f i).val : ℝ) :=
    primeLogCoordinate_rpow hx (hP (f i).val (f i).property)
  calc
    (tupleTailProduct f : ℝ) = ∏ i, ((f i).val : ℝ) := hcast
    _ = ∏ i, x ^ primeLogCoordinate x (f i).val := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (heach i).symm
    _ = x ^ ∑ i, primeLogCoordinate x (f i).val := by
      symm
      simpa using
        (Real.rpow_sum_of_pos hx0 (fun i : Fin k => primeLogCoordinate x (f i).val)
          Finset.univ)

def tupleLastPrimeChoices (I P : Finset ℕ) {k : ℕ}
    (f : Fin k → PrimeLabel P) : Finset (PrimeLabel P) :=
  Finset.univ.filter fun q => q.val * tupleTailProduct f ∈ I

def tupleHeadTailCellPairs (I P : Finset ℕ) (k : ℕ) :
    Finset (PrimeLabel P × (Fin k → PrimeLabel P)) :=
  (Finset.univ.product Finset.univ).filter fun qf =>
    qf.1.val * tupleTailProduct qf.2 ∈ I

def roughLogCell (x S w : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊x ^ w⌋₊ ⌊Real.exp (L x ^ (-S)) * x ^ w⌋₊

def squarefreeRoughCell (x S gamma w : ℝ) : Finset ℕ :=
  (roughLogCell x S w).filter fun n =>
    rough (x ^ gamma) n ∧ Squarefree n ∧ ¬ n.Prime

def roughLogCellLastChoices (x S w : ℝ) (P : Finset ℕ) {k : ℕ}
    (f : Fin k → PrimeLabel P) : Finset (PrimeLabel P) :=
  tupleLastPrimeChoices (roughLogCell x S w) P f

def simplexGridPrimeBox {k N : ℕ} (x b h : ℝ) (P : Finset ℕ)
    (j : Fin k → Fin N) (f : Fin k → PrimeLabel P) : Prop :=
  ∀ i, (f i).val ∈
    (Finset.Ioc ⌊x ^ (simplexGridLower b h j i)⌋₊
      ⌊x ^ (simplexGridUpper b h j i)⌋₊).filter Nat.Prime

lemma simplexGridPrimeBox_weight_indicator {k N : ℕ} (x b h : ℝ)
    (P : Finset ℕ) (j : Fin k → Fin N) (f : Fin k → PrimeLabel P) :
    (if simplexGridPrimeBox x b h P j f then
        (tupleTailProduct f : ℝ)⁻¹ else 0) =
      ∏ i, if (f i).val ∈
        (Finset.Ioc ⌊x ^ (simplexGridLower b h j i)⌋₊
          ⌊x ^ (simplexGridUpper b h j i)⌋₊).filter Nat.Prime then
            1 / ((f i).val : ℝ) else 0 := by
  classical
  by_cases hbox : simplexGridPrimeBox x b h P j f
  · have hmem : ∀ i,
        (f i).val ∈
          (Finset.Ioc ⌊x ^ (simplexGridLower b h j i)⌋₊
            ⌊x ^ (simplexGridUpper b h j i)⌋₊).filter Nat.Prime := by
      simpa [simplexGridPrimeBox] using hbox
    rw [if_pos hbox, tupleTailProduct_inv_eq_prod_inv]
    apply Finset.prod_congr rfl
    intro i hi
    simp [hmem i]
  · have hnot : ¬ ∀ i,
        (f i).val ∈
          (Finset.Ioc ⌊x ^ (simplexGridLower b h j i)⌋₊
            ⌊x ^ (simplexGridUpper b h j i)⌋₊).filter Nat.Prime := by
      simpa [simplexGridPrimeBox] using hbox
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    rw [if_neg hbox]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

theorem simplexGridPrimeBox_mass_eq {k N : ℕ} (x b h : ℝ)
    (P : Finset ℕ) (j : Fin k → Fin N) :
    (∑ f : Fin k → PrimeLabel P,
      if simplexGridPrimeBox x b h P j f then
        (tupleTailProduct f : ℝ)⁻¹ else 0) =
      ∏ i, simplexGridCellMass x b h P (j i).val := by
  classical
  calc
    _ = ∑ f : Fin k → PrimeLabel P,
        ∏ i, if (f i).val ∈
          (Finset.Ioc ⌊x ^ (simplexGridLower b h j i)⌋₊
            ⌊x ^ (simplexGridUpper b h j i)⌋₊).filter Nat.Prime then
              1 / ((f i).val : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro f hf
        exact simplexGridPrimeBox_weight_indicator x b h P j f
    _ = ∏ i, simplexGridCellMass x b h P (j i).val :=
      (simplexGridBoxPrimeTupleMass_eq x b h P j).symm

theorem tailTupleResidual_eq {x w : ℝ} (hx : 1 < x)
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (f : Fin k → PrimeLabel P) :
    Real.log (x ^ w / (tupleTailProduct f : ℝ)) / Analytic.L x =
      w - ∑ i, primeLogCoordinate x (f i).val := by
  have hx0 : 0 < x := by linarith
  have hQ := tupleTailProduct_eq_rpow_sum hx hP f
  rw [hQ, ← Real.rpow_sub hx0 w (∑ i, primeLogCoordinate x (f i).val),
    Real.log_rpow hx0]
  dsimp [Analytic.L]
  field_simp [ne_of_gt (Real.log_pos hx)]

theorem roughLogCellLastChoices_exponent_support {x S gamma w : ℝ}
    (hx : 1 < x) (hL : 0 < Analytic.L x) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ x ^ gamma < (p : ℝ))
    {k : ℕ} (f : Fin k → PrimeLabel P)
    (hne : (roughLogCellLastChoices x S w P f).Nonempty) :
    (∀ i, gamma < primeLogCoordinate x (f i).val) ∧
      (∑ i, primeLogCoordinate x (f i).val) ≤
        w - gamma + L x ^ (-S) / Analytic.L x := by
  have hx0 : 0 < x := by linarith
  have hQeq := tupleTailProduct_eq_rpow_sum hx (fun p hp => (hP p hp).1) f
  have hQpos : 0 < (tupleTailProduct f : ℝ) := by
    rw [hQeq]
    exact Real.rpow_pos_of_pos hx0 _
  have hcoordinates : ∀ i, gamma < primeLogCoordinate x (f i).val := by
    intro i
    have hpi := (hP (f i).val (f i).property).2
    have hpiPos : 0 < (f i).val := by exact_mod_cast (hP (f i).val (f i).property).1.pos
    have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hx0 gamma) hpi
    rw [Real.log_rpow hx0 gamma] at hlog
    apply (lt_div_iff₀ hL).2
    simpa [primeLogCoordinate, Analytic.L, mul_comm] using hlog
  obtain ⟨q, hq⟩ := hne
  have hqCell : q.val * tupleTailProduct f ∈ roughLogCell x S w := by
    simpa [roughLogCellLastChoices, tupleLastPrimeChoices] using hq
  have hqUpper : q.val * tupleTailProduct f ≤
      ⌊Real.exp (L x ^ (-S)) * x ^ w⌋₊ := (Finset.mem_Ioc.mp hqCell).2
  have hqUpperReal :
      (q.val : ℝ) * (tupleTailProduct f : ℝ) ≤ Real.exp (L x ^ (-S)) * x ^ w := by
    have hcast : ((q.val * tupleTailProduct f : ℕ) : ℝ) ≤
        (⌊Real.exp (L x ^ (-S)) * x ^ w⌋₊ : ℝ) := by exact_mod_cast hqUpper
    have hcastReal : (q.val : ℝ) * (tupleTailProduct f : ℝ) ≤
        (⌊Real.exp (L x ^ (-S)) * x ^ w⌋₊ : ℝ) := by
      simpa [Nat.cast_mul] using hcast
    exact hcastReal.trans (Nat.floor_le (by positivity))
  have hqLower : x ^ gamma < (q.val : ℝ) := (hP q.val q.property).2
  have hmul : x ^ gamma * (tupleTailProduct f : ℝ) <
      (q.val : ℝ) * (tupleTailProduct f : ℝ) :=
    mul_lt_mul_of_pos_right hqLower hQpos
  have hmul' : x ^ gamma * x ^ (∑ i, primeLogCoordinate x (f i).val) <
      Real.exp (L x ^ (-S)) * x ^ w := by
    simpa [hQeq] using lt_of_lt_of_le hmul hqUpperReal
  have hexpProduct :
      x ^ (gamma + ∑ i, primeLogCoordinate x (f i).val) <
        Real.exp (L x ^ (-S)) * x ^ w := by
    rw [Real.rpow_add hx0 gamma (∑ i, primeLogCoordinate x (f i).val)]
    exact hmul'
  have hlogProduct := Real.log_lt_log
    (Real.rpow_pos_of_pos hx0 _) hexpProduct
  rw [Real.log_rpow hx0 (gamma + ∑ i, primeLogCoordinate x (f i).val),
    Real.log_mul (Real.exp_ne_zero _) (Real.rpow_pos_of_pos hx0 w).ne',
    Real.log_exp, Real.log_rpow hx0 w] at hlogProduct
  dsimp [Analytic.L] at hlogProduct
  have hsumUpper :
      gamma + ∑ i, primeLogCoordinate x (f i).val <
        w + L x ^ (-S) / Analytic.L x := by
    have hlogProduct' :
        (gamma + ∑ i, primeLogCoordinate x (f i).val) * Analytic.L x <
          Analytic.L x ^ (-S) + w * Analytic.L x := by
      simpa [Analytic.L] using hlogProduct
    have hdiv :
        gamma + ∑ i, primeLogCoordinate x (f i).val - w <
          L x ^ (-S) / Analytic.L x := by
      apply (lt_div_iff₀ hL).2
      nlinarith [hlogProduct']
    linarith
  exact ⟨hcoordinates, by linarith⟩

noncomputable def tailPrimeGridTerm (x S w eta : ℝ) (P : Finset ℕ)
    (l : ℕ) : ℝ :=
  ∑ f : Fin (l - 1) → PrimeLabel P,
    if (roughLogCellLastChoices x S w P f).Nonempty then
      ((Real.log (x ^ w / (tupleTailProduct f : ℝ)) / L x)⁻¹ + eta) /
        (tupleTailProduct f : ℝ)
    else 0

noncomputable def tailPrimeGridMass (x S w eta : ℝ)
    (P : Finset ℕ) (K : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 2 K, tailPrimeGridTerm x S w eta P l / (l.factorial : ℝ)

theorem tailPrimeGridTerm_eq_of_cutoff (x S w eta : ℝ) (P : Finset ℕ)
    (l M : ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p)
    (hI : ∀ n ∈ roughLogCell x S w, n ≤ M) :
    tailPrimeGridTerm x S w eta P l =
      tailPrimeGridTerm x S w eta (P.filter fun p => p ≤ M) l := by
  let I := roughLogCell x S w
  let Q := P.filter fun p => p ≤ M
  let k := l - 1
  let F : ℕ → ℝ := fun n =>
    ((Real.log (x ^ w / (n : ℝ)) / L x)⁻¹ + eta) / (n : ℝ)
  have hrewrite (R : Finset ℕ) :
      tailPrimeGridTerm x S w eta R l =
        ∑ f : Fin k → PrimeLabel R,
          (if ∃ q ∈ R, q * (∏ i, (f i).val) ∈ I
            then F (∏ i, (f i).val) else 0) := by
    unfold tailPrimeGridTerm
    apply Finset.sum_congr rfl
    intro f hf
    have hnemp : (roughLogCellLastChoices x S w R f).Nonempty ↔
        ∃ q ∈ R, q * (∏ i, (f i).val) ∈ I := by
      unfold roughLogCellLastChoices tupleLastPrimeChoices
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨q.val, q.property, (Finset.mem_filter.mp hq).2⟩
      · rintro ⟨q, hqR, hq⟩
        exact ⟨⟨q, hqR⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
    simp only [hnemp]
    rfl
  have hI' : ∀ n ∈ I, n ≤ M := by simpa [I] using hI
  have hrestrict := P8Core.TailRestrictionTask_proof I P M k hP hI' F
  calc
    tailPrimeGridTerm x S w eta P l =
        ∑ f : Fin k → PrimeLabel P,
          (if ∃ q ∈ P, q * (∏ i, (f i).val) ∈ I
            then F (∏ i, (f i).val) else 0) := hrewrite P
    _ = ∑ f : Fin k → PrimeLabel Q,
          (if ∃ q ∈ Q, q * (∏ i, (f i).val) ∈ I
            then F (∏ i, (f i).val) else 0) := hrestrict
    _ = tailPrimeGridTerm x S w eta Q l := (hrewrite Q).symm

theorem primeTupleCell_card_le_tail_sum (I P : Finset ℕ) (k : ℕ) :
    (primeTupleCellFinset I P (k + 1)).card ≤
      ∑ f : Fin k → PrimeLabel P, (tupleLastPrimeChoices I P f).card := by
  classical
  let E := Fin.consEquiv (fun _ : Fin (k + 1) => PrimeLabel P)
  have hcard : (primeTupleCellFinset I P (k + 1)).card =
      (tupleHeadTailCellPairs I P k).card := by
    apply Finset.card_equiv E.symm
    intro z
    simp only [primeTupleCellFinset, tupleHeadTailCellPairs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simp [E, tupleProduct, tupleTailProduct, Fin.consEquiv, Fin.tail,
      Fin.prod_univ_succ, Finset.mem_attach]
  let C := tupleHeadTailCellPairs I P k
  let T := (Finset.univ : Finset (Fin k → PrimeLabel P))
  have hmaps : Set.MapsTo Prod.snd
      (C : Set (PrimeLabel P × (Fin k → PrimeLabel P)))
      (T : Set (Fin k → PrimeLabel P)) := by
    intro qf hqf
    simp [T]
  have hcardFibers := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (f : Fin k → PrimeLabel P) :
      (C.filter fun qf => qf.2 = f).card ≤ (tupleLastPrimeChoices I P f).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro qf hqf
      have hqf' := Finset.mem_filter.mp hqf
      have hpair := Finset.mem_filter.mp hqf'.1
      simp [tupleLastPrimeChoices]
      rw [← hqf'.2]
      exact hpair.2
    · intro qf hqf qf' hqf' hfst
      have hf := (Finset.mem_filter.mp hqf).2
      have hf' := (Finset.mem_filter.mp hqf').2
      exact Prod.ext hfst (hf.trans hf'.symm)
  calc
    (primeTupleCellFinset I P (k + 1)).card = C.card := hcard
    _ = ∑ f ∈ T, (C.filter fun qf => qf.2 = f).card := hcardFibers
    _ ≤ ∑ f ∈ T, (tupleLastPrimeChoices I P f).card := by
      apply Finset.sum_le_sum
      intro f hf
      exact hfiber f
    _ = ∑ f : Fin k → PrimeLabel P, (tupleLastPrimeChoices I P f).card := by
      simp [T]

theorem squarefreeRoughCell_tuple_count_bound (x S gamma w : ℝ) (P : Finset ℕ)
    (K : ℕ)
    (hP : ∀ n, n ∈ squarefreeRoughCell x S gamma w → n.primeFactors ⊆ P)
    (hlo : ∀ n, n ∈ squarefreeRoughCell x S gamma w →
      2 ≤ n.primeFactors.card)
    (hhi : ∀ n, n ∈ squarefreeRoughCell x S gamma w →
      n.primeFactors.card ≤ K) :
    ((squarefreeRoughCell x S gamma w).card : ℝ) ≤
      ∑ l ∈ Finset.Icc 2 K,
        (primeTupleCellFinset (roughLogCell x S w) P l).card / (l.factorial : ℝ) := by
  classical
  let I := roughLogCell x S w
  let C := squarefreeRoughCell x S gamma w
  let F : ℕ → Finset ℕ := fun l => squarefreeCellFinset I P l
  have hcover : C ⊆ (Finset.Icc 2 K).biUnion F := by
    intro n hn
    change n ∈ squarefreeRoughCell x S gamma w at hn
    unfold squarefreeRoughCell at hn
    have hnC := Finset.mem_filter.mp hn
    have hnI := hnC.1
    have hnRough := hnC.2.1
    have hnSQ := hnC.2.2.1
    let l := n.primeFactors.card
    have hlRange : l ∈ Finset.Icc 2 K := by
      exact Finset.mem_Icc.mpr ⟨hlo n hn, hhi n hn⟩
    have hnF : n ∈ F l := by
      apply Finset.mem_filter.mpr
      refine ⟨hnI, ?_⟩
      exact ⟨hnSQ, ⟨rfl, hP n hn⟩⟩
    exact Finset.mem_biUnion.mpr ⟨l,hlRange,hnF⟩
  have hcardNat : C.card ≤ ∑ l ∈ Finset.Icc 2 K, (F l).card := by
    calc
      C.card ≤ ((Finset.Icc 2 K).biUnion F).card := Finset.card_le_card hcover
      _ ≤ ∑ l ∈ Finset.Icc 2 K, (F l).card := Finset.card_biUnion_le
  have hcardReal : (C.card : ℝ) ≤
      ∑ l ∈ Finset.Icc 2 K, ((F l).card : ℝ) := by exact_mod_cast hcardNat
  calc
    (C.card : ℝ) ≤ ∑ l ∈ Finset.Icc 2 K, ((F l).card : ℝ) := hcardReal
    _ ≤ ∑ l ∈ Finset.Icc 2 K,
        (primeTupleCellFinset I P l).card / (l.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      have hfacNat := squarefreeCell_factorial_card_le I P l
      have hfac : ((F l).card : ℝ) * (l.factorial : ℝ) ≤
          (primeTupleCellFinset I P l).card := by
        exact_mod_cast hfacNat
      have hfacpos : 0 < (l.factorial : ℝ) := by positivity
      exact (le_div_iff₀ hfacpos).2 hfac


end Erdos821.P8Grid
