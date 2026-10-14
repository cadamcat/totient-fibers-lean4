import Erdos821.Blueprint.Extraction
import Mathlib.NumberTheory.AbelSummation

/-! Finite-sum bookkeeping for the §6 extraction argument. -/
noncomputable section
open scoped BigOperators ContDiff
namespace Erdos821.P10
open Filter
open Erdos821.Blueprint
attribute [local instance] Classical.propDecidable

/-- Split the candidate mass into prime and nonprime values of `2u+1`. -/
theorem mass_eq_prime_add_nonprime (C : CandidateData) (x : ℝ) (jstar : ℕ) :
    C.mass x jstar = C.primeMass x jstar +
      ∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => ¬ Nat.Prime (2 * u + 1)),
        C.weighted x jstar u := by
  classical
  unfold CandidateData.mass CandidateData.primeMass
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 ⌊2 * x⌋₊) (fun u => Nat.Prime (2 * u + 1))
    (fun u => C.weighted x jstar u)]

/-- A nonprime integer at least two has a proper prime factor. -/
theorem composite_has_proper_prime_factor {n : ℕ} (hn : 2 ≤ n)
    (hprime : ¬ Nat.Prime n) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p < n := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  refine ⟨p, hp, hpdvd, ?_⟩
  by_contra hlt
  have hle : n ≤ p := Nat.le_of_not_gt hlt
  have hp_le : p ≤ n := Nat.le_of_dvd (by omega) hpdvd
  have : p = n := Nat.le_antisymm hp_le hle
  subst n
  exact hprime hp

/-- The cofactor left after selecting the least prime factor is rough above
any cutoff strictly below that factor. -/
theorem minFac_cofactor_rough {y : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hy : y < (N.minFac : ℝ)) :
    Analytic.rough y (N / N.minFac) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hpPrime : Nat.Prime N.minFac := Nat.minFac_prime (by omega)
  have hpdiv : N.minFac ∣ N := Nat.minFac_dvd N
  have hpLe : N.minFac ≤ N := Nat.minFac_le hNpos
  have hquot : 0 < N / N.minFac := Nat.div_pos hpLe hpPrime.pos
  refine ⟨hquot, ?_⟩
  intro q hq hqd
  have hmul : (N / N.minFac) * N.minFac = N := Nat.div_mul_cancel hpdiv
  have hqN : q ∣ N := by
    rw [← hmul]
    exact dvd_mul_of_dvd_left hqd N.minFac
  have hpq : N.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqN
  exact lt_of_lt_of_le hy (Nat.cast_le.mpr hpq)

/-- A survivor of the odd-prime presieve has no prime divisor up to its
cutoff. -/
theorem survivor_prime_factor_gt (y : ℝ) (u p : ℕ) (hy : 1 ≤ y)
    (hp : Nat.Prime p) (hpdvd : p ∣ 2 * u + 1)
    (hSurv : ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1) :
    y < (p : ℝ) := by
  by_contra hnot
  have hpy : (p : ℝ) ≤ y := le_of_not_gt hnot
  have hpne2 : p ≠ 2 := by
    intro heq
    subst p
    have hnotTwo : ¬ 2 ∣ 2 * u + 1 := by omega
    exact hnotTwo hpdvd
  have hpFloor : p ≤ ⌊y⌋₊ :=
    (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ y)).2 hpy
  have hpUp : p ∈ primesUpTo y :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpFloor⟩, hp⟩
  have hpErase : p ∈ (primesUpTo y).erase 2 :=
    Finset.mem_erase.mpr ⟨hpne2, hpUp⟩
  exact hSurv p hpErase hpdvd

/-- For an odd integer, surviving the odd-prime sieve through `y` is exactly
the condition that it is `y`-rough. -/
theorem rough_iff_survives_odd_prime_sieve (y : ℝ) (n : ℕ) (hy : 1 ≤ y)
    (hOdd : Odd n) :
    Analytic.rough y n ↔
      ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ n := by
  constructor
  · rintro ⟨hn, hrough⟩ q hq hqdiv
    have hqne : q ≠ 2 := (Finset.mem_erase.mp hq).1
    have hqUp := Finset.mem_erase.mp hq |>.2
    have hqData := Finset.mem_filter.mp hqUp
    have hqle := (Finset.mem_Icc.mp hqData.1).2
    have hqcast : (q : ℝ) ≤ y := le_trans (Nat.cast_le.mpr hqle)
      (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
    exact (not_lt_of_ge hqcast) (hrough q hqData.2 hqdiv)
  · intro hSurv
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      simp at hOdd
    refine ⟨Nat.pos_of_ne_zero hn0, ?_⟩
    intro p hp hpdiv
    by_contra hnot
    have hple : (p : ℝ) ≤ y := le_of_not_gt hnot
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      have heven : Even n := even_iff_two_dvd.mpr hpdiv
      have hnotOdd : ¬ Odd n := Nat.not_odd_iff_even.mpr heven
      exact hnotOdd hOdd
    have hpFloor : p ≤ ⌊y⌋₊ :=
      (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ y)).2 hple
    have hpUp : p ∈ primesUpTo y :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpFloor⟩, hp⟩
    exact hSurv p (Finset.mem_erase.mpr ⟨hpne2, hpUp⟩) hpdiv

/-- Raising the roughness cutoff can only strengthen roughness. -/
theorem rough_mono_cutoff {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hn : Analytic.rough b n) : Analytic.rough a n := by
  rcases hn with ⟨hnpos, hfactor⟩
  refine ⟨hnpos, ?_⟩
  intro p hp hpdvd
  exact lt_of_le_of_lt hab (hfactor p hp hpdvd)

/-- The roughness proxy and its underlying constant are nonnegative. -/
theorem proxyConstant_rough_nonneg (x S γ : ℝ) (m : ℕ) :
    0 ≤ proxyConstant (.rough γ) x S m := by
  unfold proxyConstant
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro n hn
    by_cases hr : Analytic.rough (x ^ γ) n <;> simp [test, hr]
  · exact Nat.cast_nonneg _

theorem proxy_rough_nonneg (x S γ : ℝ) (m : ℕ) :
    0 ≤ proxy (.rough γ) x S m := by
  unfold proxy
  split_ifs
  · exact proxyConstant_rough_nonneg x S γ m
  · norm_num

/-- If `N` is rough, each positive divisor cofactor is rough as well. -/
theorem rough_div_factor {W : ℝ} {N p : ℕ}
    (hrough : Analytic.rough W N) (hpdiv : p ∣ N) (hppos : 0 < p) :
    Analytic.rough W (N / p) := by
  have hpLe : p ≤ N := Nat.le_of_dvd hrough.1 hpdiv
  have hquotpos : 0 < N / p := Nat.div_pos hpLe hppos
  refine ⟨hquotpos, ?_⟩
  intro q hq hqd
  have hmul : N / p * p = N := Nat.div_mul_cancel hpdiv
  have hqN : q ∣ N := by
    rw [← hmul]
    exact dvd_mul_of_dvd_left hqd p
  exact hrough.2 q hq hqN

/-- The product of two rough positive integers is rough. -/
theorem rough_mul {W : ℝ} {m n : ℕ}
    (hm : Analytic.rough W m) (hn : Analytic.rough W n) :
    Analytic.rough W (m * n) := by
  rcases hm with ⟨hmpos, hmfactor⟩
  rcases hn with ⟨hnpos, hnfactor⟩
  refine ⟨Nat.mul_pos hmpos hnpos, ?_⟩
  intro p hp hpdvd
  rcases hp.dvd_mul.mp hpdvd with hpm | hpn
  · exact hmfactor p hp hpm
  · exact hnfactor p hp hpn

/-- An odd presieve survivor is rough, and its quotient by a positive prime
factor remains rough. -/
theorem survivor_cofactor_rough (W : ℝ) (u p : ℕ) (hW : 1 ≤ W)
    (hpdiv : p ∣ 2 * u + 1) (hppos : 0 < p)
    (hSurv : ∀ q ∈ (primesUpTo W).erase 2, ¬ q ∣ 2 * u + 1) :
    Analytic.rough W ((2 * u + 1) / p) := by
  have hodd : Odd (2 * u + 1) := by simp
  have hrough := (rough_iff_survives_odd_prime_sieve W (2 * u + 1) hW hodd).2 hSurv
  exact rough_div_factor hrough hpdiv hppos

/-- On a rough cofactor, the proxy is its constant-cell value, so a density
upper bound is a pointwise proxy upper bound. -/
theorem proxy_cofactor_bound (x S γ Q : ℝ) (u p : ℕ)
    (hrough : Analytic.rough (Analytic.W x) ((2 * u + 1) / p))
    (hConst : proxyConstant (.rough γ) x S ((2 * u + 1) / p) ≤ Q) :
    0 ≤ proxy (.rough γ) x S ((2 * u + 1) / p) ∧
      proxy (.rough γ) x S ((2 * u + 1) / p) ≤ Q := by
  have hproxyEq : proxy (.rough γ) x S ((2 * u + 1) / p) =
      proxyConstant (.rough γ) x S ((2 * u + 1) / p) := by
    simp [proxy, hrough]
  rw [hproxyEq]
  exact ⟨proxyConstant_rough_nonneg x S γ _, hConst⟩

/-- The sieve survivor condition plus a fixed-cell density estimate bounds the
cofactor proxy at each prime divisor. -/
theorem proxy_cofactor_bound_from_sieve (x S γ Q : ℝ) (u p : ℕ)
    (hW : 1 ≤ Analytic.W x) (hdiv : p ∣ 2 * u + 1) (hp : Nat.Prime p)
    (hSurv : ∀ q ∈ (primesUpTo (Analytic.W x)).erase 2,
      ¬ q ∣ 2 * u + 1)
    (hConst : proxyConstant (.rough γ) x S ((2 * u + 1) / p) ≤ Q) :
    0 ≤ proxy (.rough γ) x S ((2 * u + 1) / p) ∧
      proxy (.rough γ) x S ((2 * u + 1) / p) ≤ Q := by
  have hrough := survivor_cofactor_rough (Analytic.W x) u p hW hdiv hp.pos hSurv
  exact proxy_cofactor_bound x S γ Q u p hrough hConst

/-- The rough-cofactor density clause of ProxyInputs, specialized to one fixed
exponent bin. -/
theorem proxy_rough_bin_density_event (hp : ProxyInputs)
    (b κ S γ γ' ε : ℝ) (hb : 0 < b) (hκ : 0 < κ)
    (hκsmall : κ < 1 / 50) (hS : 0 < S) (hbg : b ≤ γ)
    (hgg : γ < γ') (hTop : γ' ≤ 1 / 2 - κ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ m n u : ℕ,
      m * n = 2 * u + 1 → x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
      γ < Real.log n / Analytic.L x → Real.log n / Analytic.L x ≤ γ' →
      proxyConstant (.rough γ) x S m ≤
        (sSup ((fun a : ℝ => roughDensity γ (1 - a)) '' Set.Icc γ γ') + ε) /
          (Analytic.L x * sieveProduct (Analytic.W x)) :=
  hp.densities.2 b κ S γ γ' ε hb hκ hκsmall hS hbg hgg hTop hε

/-- Exponent conditions on a factor are equivalent to the logarithmic bin
conditions used by ProxyInputs. -/
theorem log_factor_mem_exponent_bin (x p γ γ' : ℝ) (hx : 1 < x)
    (hγ : 0 < γ) (hγ' : 0 < γ')
    (hpLo : x ^ γ < p) (hpHi : p ≤ x ^ γ') :
    γ < Real.log p / Analytic.L x ∧ Real.log p / Analytic.L x ≤ γ' := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hlogx : 0 < Analytic.L x := by
    dsimp [Analytic.L]
    exact Real.log_pos hx
  have hpPos : 0 < p := lt_trans (Real.rpow_pos_of_pos hxpos γ) hpLo
  have hlogLo := Real.log_lt_log (Real.rpow_pos_of_pos hxpos γ) hpLo
  have hlogHi := Real.log_le_log hpPos hpHi
  rw [Real.log_rpow hxpos γ] at hlogLo
  rw [Real.log_rpow hxpos γ'] at hlogHi
  constructor
  · rw [lt_div_iff₀ hlogx]
    simpa [Analytic.L] using hlogLo
  · rw [div_le_iff₀ hlogx]
    simpa [Analytic.L, mul_comm] using hlogHi

/-- A proxy difference has coefficient norm at most one whenever the proxy is
between zero and one on its interval. -/
theorem proxyDifference_norm_le_one (I : FactorTest) (x S lo hi : ℝ)
    (hproxy : ∀ n : ℕ, lo ≤ (n : ℝ) → (n : ℝ) ≤ hi →
      0 ≤ proxy I x S n ∧ proxy I x S n ≤ 1) :
    ∀ n, ‖proxyDifference I x S lo hi n‖ ≤ 1 := by
  intro n
  have htest : 0 ≤ test I x n ∧ test I x n ≤ 1 := by
    cases I with
    | prime => by_cases hn : n.Prime <;> simp [test, hn]
    | rough γ => by_cases hn : Analytic.rough (x ^ γ) n <;> simp [test, hn]
  by_cases hn : lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi
  · rcases htest with ⟨ht0, ht1⟩
    rcases hproxy n hn.1 hn.2 with ⟨hp0, hp1⟩
    have hdiff : |test I x n - proxy I x S n| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith
    rw [proxyDifference]
    simp only [if_pos hn, Complex.norm_real]
    exact hdiff
  · simp [proxyDifference, hn]

/-- If a roughness test differs from its proxy, its support lies on W-rough
integers once `W` lies below the test cutoff. -/
theorem roughProxyDifference_support (x S lo hi γ : ℝ) (n : ℕ)
    (hW : Analytic.W x ≤ x ^ γ)
    (hDiff : proxyDifference (.rough γ) x S lo hi n ≠ 0) :
    Analytic.rough (Analytic.W x) n := by
  by_cases hrough : Analytic.rough (x ^ γ) n
  · exact rough_mono_cutoff hW hrough
  · have htest : test (.rough γ) x n = 0 := by simp [test, hrough]
    have hproxy : proxy (.rough γ) x S n ≠ 0 := by
      by_contra hzero
      apply hDiff
      simp [proxyDifference, htest, hzero]
    unfold proxy at hproxy
    by_cases hroughW : Analytic.rough (Analytic.W x) n
    · exact hroughW
    · simp [hroughW] at hproxy

/-- The auxiliary cutoff `W=exp(sqrt(log x))` is below any fixed positive
power of `x` for all sufficiently large `x`. -/
theorem eventually_W_le_rpow (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, Analytic.W x ≤ x ^ γ := by
  have hlog := (Real.tendsto_log_atTop).eventually (eventually_ge_atTop (γ⁻¹ ^ 2))
  filter_upwards [hlog, eventually_gt_atTop (1 : ℝ)] with x hxlog hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hLnonneg : 0 ≤ Analytic.L x := by
    dsimp [Analytic.L]
    exact Real.log_nonneg (by linarith)
  have hγinv : 0 < γ⁻¹ := inv_pos.mpr hγ
  have hscale : 1 ≤ γ ^ 2 * Analytic.L x := by
    calc
      1 = γ ^ 2 * γ⁻¹ ^ 2 := by field_simp [ne_of_gt hγ]
      _ ≤ γ ^ 2 * Analytic.L x := by
        apply mul_le_mul_of_nonneg_left hxlog
        positivity
  have hroot : Real.sqrt (Analytic.L x) ≤ γ * Analytic.L x := by
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg hγ.le hLnonneg, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hscale hLnonneg
    nlinarith [hmul]
  change Real.exp (Real.sqrt (Analytic.L x)) ≤ x ^ γ
  rw [Real.rpow_def_of_pos hxpos]
  have hroot' : Real.sqrt (Real.log x) ≤ Real.log x * γ := by
    simpa [Analytic.L, mul_comm] using hroot
  exact Real.exp_le_exp.mpr hroot'

/-- The auxiliary sieve cutoff tends to infinity. -/
theorem eventually_two_le_W :
    ∀ᶠ x : ℝ in atTop, 2 ≤ Analytic.W x := by
  have hlog := (Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop ((Real.log 2) ^ 2))
  filter_upwards [hlog, eventually_gt_atTop (1 : ℝ)] with x hlog hx
  have hlogPos : 0 < Real.log x := Real.log_pos hx
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hroot : Real.log 2 ≤ Real.sqrt (Real.log x) := by
    have hsqrtSq := Real.sq_sqrt (le_of_lt hlogPos)
    have hrootNonneg := Real.sqrt_nonneg (Real.log x)
    nlinarith
  change 2 ≤ Real.exp (Real.sqrt (Real.log x))
  calc
    2 = Real.exp (Real.log 2) :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
    _ ≤ Real.exp (Real.sqrt (Real.log x)) := Real.exp_le_exp.mpr hroot

/-- The auxiliary cutoff tends to infinity with `x`. -/
theorem tendsto_W_atTop : Tendsto Analytic.W atTop atTop := by
  change Tendsto (fun x : ℝ => Real.exp (Real.sqrt (Real.log x))) atTop atTop
  exact Real.tendsto_exp_atTop.comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

/-- The shifted sieve product ratio approaches its supplied singular series
along the auxiliary cutoff. -/
theorem eventually_shiftedSieveRatio_W_le
    (hp : ProxyInputs) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      shiftedSieveProduct (Analytic.W x) / sieveProduct (Analytic.W x) ≤
        singularSeries + η := by
  have hlimit := hp.products.2.comp tendsto_W_atTop
  have hUpper : ∀ᶠ x : ℝ in atTop,
      shiftedSieveProduct (Analytic.W x) / sieveProduct (Analytic.W x) <
        singularSeries + η :=
    hlimit.eventually (Iio_mem_nhds (by linarith [hη]))
  exact hUpper.mono fun x hx => le_of_lt hx

/-- Mertens' product asymptotic at `W(x)` implies that the denominator in
the rough-bin proxy coefficient eventually exceeds one. -/
theorem eventually_one_le_log_sieveProduct_W (hc : ClassicalInputs) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ Analytic.L x * sieveProduct (Analytic.W x) := by
  let c : ℝ := Real.exp (-Real.eulerMascheroniConstant) / 2
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hMertens := hc.mertens.2.comp tendsto_W_atTop
  have hMertensLower : ∀ᶠ x : ℝ in atTop,
      c ≤ Real.log (Analytic.W x) * sieveProduct (Analytic.W x) :=
    hMertens.eventually (Ici_mem_nhds (by
      dsimp [c]
      have hE : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
      linarith))
  have hsqrtT : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hsqrt : ∀ᶠ x : ℝ in atTop,
      c⁻¹ ≤ Real.sqrt (Analytic.L x) := by
    have h := hsqrtT.eventually (eventually_ge_atTop c⁻¹)
    simpa [Analytic.L] using h
  filter_upwards [hMertensLower, hsqrt, eventually_gt_atTop (1 : ℝ)]
    with x hMertens hsqrt hx
  have hlogW : Real.log (Analytic.W x) = Real.sqrt (Analytic.L x) := by
    change Real.log (Real.exp (Real.sqrt (Real.log x))) =
      Real.sqrt (Real.log x)
    rw [Real.log_exp]
  have hprodLower : c ≤ Real.sqrt (Analytic.L x) *
      sieveProduct (Analytic.W x) := by rw [← hlogW]; exact hMertens
  have hsmall : 1 ≤ Real.sqrt (Analytic.L x) * c := by
    calc
      1 = c⁻¹ * c := by field_simp [ne_of_gt hcpos]
      _ ≤ Real.sqrt (Analytic.L x) * c :=
        mul_le_mul_of_nonneg_right hsqrt hcpos.le
  have hlarge := mul_le_mul_of_nonneg_left hprodLower
    (Real.sqrt_nonneg (Analytic.L x))
  have hLpos : 0 < Analytic.L x := by
    dsimp [Analytic.L]
    exact Real.log_pos hx
  have hLsq : Real.sqrt (Analytic.L x) * Real.sqrt (Analytic.L x) =
      Analytic.L x := by
    have h := Real.sq_sqrt hLpos.le
    nlinarith [h]
  calc
    1 ≤ Real.sqrt (Analytic.L x) *
          (Real.sqrt (Analytic.L x) * sieveProduct (Analytic.W x)) :=
        hsmall.trans hlarge
    _ = (Real.sqrt (Analytic.L x) * Real.sqrt (Analytic.L x)) *
          sieveProduct (Analytic.W x) := by ring
    _ = Analytic.L x * sieveProduct (Analytic.W x) := by rw [hLsq]

/-- A cofactor of a candidate integer paired with a prime in an unbalanced
bin stays inside the proxy's fixed ambient power interval. -/
theorem eventually_cofactor_proxy_ambient (b γ γ' : ℝ) (κ : ℝ)
    (hb : 0 < b) (hγ : b ≤ γ) (hγlt : γ < γ')
    (hγ' : γ' ≤ 1 / 2 - κ)
    (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in atTop, ∀ u p : ℕ,
      1 < x → x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
      p ∣ 2 * u + 1 → Nat.Prime p → x ^ γ < (p : ℝ) → (p : ℝ) ≤ x ^ γ' →
      x ^ (b / 4) ≤ (((2 * u + 1) / p : ℕ) : ℝ) ∧
        (((2 * u + 1) / p : ℕ) : ℝ) ≤ x ^ (1 - b / 4) := by
  have hbpos : 0 < 3 * b / 4 := by positivity
  have hFive : ∀ᶠ x : ℝ in atTop, 5 ≤ x ^ (3 * b / 4) :=
    (tendsto_rpow_atTop hbpos).eventually (eventually_ge_atTop 5)
  filter_upwards [hFive] with x hxFive
  intro u p hx huLo huHi hdiv hpPrime hpLo hpHi
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hxle : 1 ≤ x := hx.le
  have hpowγ : x ^ b ≤ x ^ γ := Real.rpow_le_rpow_of_exponent_le hxle hγ
  have hpLower : x ^ b < (p : ℝ) := lt_of_le_of_lt hpowγ hpLo
  have hγ'half : γ' < 1 / 2 := lt_of_le_of_lt hγ'
    (by nlinarith [hκ])
  have hpowHalf : x ^ γ' ≤ x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hxle hγ'half.le
  have hpUpper : (p : ℝ) ≤ x ^ (1 / 2 : ℝ) := le_trans hpHi hpowHalf
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hcastN : ((2 * u + 1 : ℕ) : ℝ) = 2 * (u : ℝ) + 1 := by norm_cast
  have hNLoReal : 2 * x ≤ ((2 * u + 1 : ℕ) : ℝ) := by
    rw [hcastN]
    nlinarith [huLo]
  have hNHi : ((2 * u + 1 : ℕ) : ℝ) ≤ 5 * x := by
    rw [hcastN]
    nlinarith [huHi, hx]
  have hmulNat : (2 * u + 1) / p * p = 2 * u + 1 := Nat.div_mul_cancel hdiv
  have hmul : (((2 * u + 1) / p : ℕ) : ℝ) * (p : ℝ) =
      ((2 * u + 1 : ℕ) : ℝ) := by exact_mod_cast hmulNat
  have hmEq : (((2 * u + 1) / p : ℕ) : ℝ) =
      ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) := by
    calc
      (((2 * u + 1) / p : ℕ) : ℝ) =
          ((((2 * u + 1) / p : ℕ) : ℝ) * (p : ℝ)) / (p : ℝ) := by
            field_simp [ne_of_gt hp0]
      _ = ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) := by rw [hmul]
  have hhalf : x / x ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
    calc
      x / x ^ (1 / 2 : ℝ) = x ^ (1 : ℝ) / x ^ (1 / 2 : ℝ) := by simp
      _ = x ^ ((1 : ℝ) - 1 / 2) := by rw [← Real.rpow_sub hxpos]
      _ = x ^ (1 / 2 : ℝ) := by congr 1 <;> ring
  have hmultEq : 2 * x ^ (1 / 2 : ℝ) =
      2 * x / x ^ (1 / 2 : ℝ) := by
    calc
      2 * x ^ (1 / 2 : ℝ) = 2 * (x / x ^ (1 / 2 : ℝ)) := by rw [hhalf]
      _ = 2 * x / x ^ (1 / 2 : ℝ) := by ring
  have hLower : x ^ (b / 4) ≤ (((2 * u + 1) / p : ℕ) : ℝ) := by
    have hExp : b / 4 ≤ (1 / 2 : ℝ) := by linarith [hγ, hγlt, hγ'half]
    have hpow : x ^ (b / 4) ≤ x ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hxle hExp
    have hdiv1 : 2 * x / x ^ (1 / 2 : ℝ) ≤ 2 * x / (p : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpUpper
    have hdiv2 : 2 * x / (p : ℝ) ≤ ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) :=
      div_le_div_of_nonneg_right hNLoReal (le_of_lt hp0)
    rw [hmEq]
    calc
      x ^ (b / 4) ≤ x ^ (1 / 2 : ℝ) := hpow
      _ ≤ 2 * x / x ^ (1 / 2 : ℝ) := by
        have hhalfNonneg : 0 ≤ x ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _
        have hsimple : x ^ (1 / 2 : ℝ) ≤ 2 * x ^ (1 / 2 : ℝ) := by nlinarith
        calc
          x ^ (1 / 2 : ℝ) ≤ 2 * x ^ (1 / 2 : ℝ) := hsimple
          _ = 2 * x / x ^ (1 / 2 : ℝ) := hmultEq
      _ ≤ 2 * x / (p : ℝ) := hdiv1
      _ ≤ _ := hdiv2
  have hxdiv : x / x ^ b = x ^ (1 - b) := by
    simpa using (Real.rpow_sub hxpos (1 : ℝ) b).symm
  have hcofactorUpper : (((2 * u + 1) / p : ℕ) : ℝ) ≤
      5 * x ^ (1 - b) := by
    rw [hmEq]
    have hnum : ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) ≤ 5 * x / (p : ℝ) :=
      div_le_div_of_nonneg_right hNHi (le_of_lt hp0)
    have hpLower' : x ^ b ≤ (p : ℝ) := hpLower.le
    have hden : 5 * x / (p : ℝ) ≤ 5 * x / x ^ b :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hxpos _) hpLower'
    calc
      _ ≤ 5 * x / (p : ℝ) := hnum
      _ ≤ 5 * x / x ^ b := hden
      _ = 5 * x ^ (1 - b) := by
        calc
          5 * x / x ^ b = 5 * (x / x ^ b) := by ring
          _ = 5 * x ^ (1 - b) := by rw [hxdiv]
  have hUpper : 5 * x ^ (1 - b) ≤ x ^ (1 - b / 4) := by
    have hxPowPos : 0 ≤ x ^ (1 - b) :=
      Real.rpow_nonneg (by linarith : 0 ≤ x) _
    calc
      5 * x ^ (1 - b) ≤ x ^ (3 * b / 4) * x ^ (1 - b) :=
        mul_le_mul_of_nonneg_right hxFive hxPowPos
      _ = x ^ (1 - b / 4) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
  exact ⟨hLower, le_trans hcofactorUpper hUpper⟩

/-- Every positive integer lies in its unique half-open dyadic block. -/
theorem mem_nat_dyadicBlock (n : ℕ) (hn : 0 < n) :
    n ∈ Finset.Ico (2 ^ Nat.log 2 n) (2 ^ (Nat.log 2 n + 1)) := by
  have hlo : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hhi : n < 2 ^ (Nat.log 2 n).succ := Nat.lt_pow_succ_log_self (by norm_num) n
  simpa [Nat.succ_eq_add_one] using Finset.mem_Ico.mpr ⟨hlo, hhi⟩

/-- Membership in a dyadic block is characterized by the natural logarithm. -/
theorem mem_nat_dyadicBlock_iff (n k : ℕ) (hn : 0 < n) :
    n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) ↔ Nat.log 2 n = k := by
  constructor
  · intro hmem
    have hlo : 2 ^ k ≤ n := (Finset.mem_Ico.mp hmem).1
    have hle : k ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hlo
    have hhi := (Finset.mem_Ico.mp hmem).2
    have hlt : Nat.log 2 n < k + 1 := Nat.log_lt_of_lt_pow hn.ne' hhi
    omega
  · intro hlog
    have hlo : 2 ^ k ≤ n := by simpa [hlog] using Nat.pow_log_le_self 2 hn.ne'
    have hhi : n < 2 ^ (k + 1) := by
      simpa [hlog, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    exact Finset.mem_Ico.mpr ⟨hlo, hhi⟩

/-- A dyadic block meeting `(0,Y)` has an index in a finite range. -/
theorem exists_nat_dyadicBlock_below (n Y : ℕ) (hn : 0 < n) (hny : n < Y) :
    ∃ k ∈ Finset.range (Nat.log 2 Y + 1),
      n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
  let k := Nat.log 2 n
  have hk : k ≤ Nat.log 2 Y := Nat.log_mono_right hny.le
  refine ⟨k, Finset.mem_range.mpr (by dsimp [k]; omega), ?_⟩
  simpa [k] using mem_nat_dyadicBlock n hn

/-- Reindex a finite product box by the unique pair of natural dyadic blocks
containing its coordinates. -/
theorem sum_nat_pair_dyadic_boxes (K : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ m ∈ Finset.Ico 1 (2 ^ K), ∑ n ∈ Finset.Ico 1 (2 ^ K), f m n) =
      ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
        ∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          ∑ n ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), f m n := by
  classical
  let S := Finset.Ico 1 (2 ^ K) ×ˢ Finset.Ico 1 (2 ^ K)
  let T := Finset.range K ×ˢ Finset.range K
  let g : ℕ × ℕ → ℕ × ℕ := fun z => (Nat.log 2 z.1, Nat.log 2 z.2)
  have hmap : ∀ z ∈ S, g z ∈ T := by
    intro z hz
    have hz' : z ∈ Finset.Ico 1 (2 ^ K) ×ˢ Finset.Ico 1 (2 ^ K) := by
      simpa [S] using hz
    rcases Finset.mem_product.mp hz' with ⟨hm, hn⟩
    have hmpos : z.1 ≠ 0 := by
      have := (Finset.mem_Ico.mp hm).1
      omega
    have hnpos : z.2 ≠ 0 := by
      have := (Finset.mem_Ico.mp hn).1
      omega
    have hk : Nat.log 2 z.1 < K :=
      Nat.log_lt_of_lt_pow hmpos (Finset.mem_Ico.mp hm).2
    have hl : Nat.log 2 z.2 < K :=
      Nat.log_lt_of_lt_pow hnpos (Finset.mem_Ico.mp hn).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hk, Finset.mem_range.mpr hl⟩
  have hFiber (k l : ℕ) (hk : k ∈ Finset.range K) (hl : l ∈ Finset.range K) :
      S.filter (fun z => g z = (k, l)) =
        Finset.Ico (2 ^ k) (2 ^ (k + 1)) ×ˢ Finset.Ico (2 ^ l) (2 ^ (l + 1)) := by
    ext z
    rcases z with ⟨m, n⟩
    simp only [Finset.mem_filter, S, Finset.mem_product, g]
    constructor
    · rintro ⟨⟨hmS, hnS⟩, heq⟩
      have hmk : Nat.log 2 m = k := congrArg Prod.fst heq
      have hnk : Nat.log 2 n = l := congrArg Prod.snd heq
      have hmpos : 0 < m := by
        have hge : 1 ≤ m := (Finset.mem_Ico.mp hmS).1
        omega
      have hnpos : 0 < n := by
        have hge : 1 ≤ n := (Finset.mem_Ico.mp hnS).1
        omega
      exact ⟨(mem_nat_dyadicBlock_iff m k hmpos).2 hmk,
        (mem_nat_dyadicBlock_iff n l hnpos).2 hnk⟩
    · rintro ⟨hmBlock, hnBlock⟩
      have hklt : k < K := Finset.mem_range.mp hk
      have hllt : l < K := Finset.mem_range.mp hl
      have hmpos : 0 < m := by
        have hge : 1 ≤ m := le_trans (Nat.one_le_pow k 2 (by norm_num))
          (Finset.mem_Ico.mp hmBlock).1
        omega
      have hnpos : 0 < n := by
        have hge : 1 ≤ n := le_trans (Nat.one_le_pow l 2 (by norm_num))
          (Finset.mem_Ico.mp hnBlock).1
        omega
      have hmk : Nat.log 2 m = k := (mem_nat_dyadicBlock_iff m k hmpos).1 hmBlock
      have hnk : Nat.log 2 n = l := (mem_nat_dyadicBlock_iff n l hnpos).1 hnBlock
      have hpowK : 2 ^ (k + 1) ≤ 2 ^ K := pow_le_pow_right' (by norm_num) (by omega)
      have hpowL : 2 ^ (l + 1) ≤ 2 ^ K := pow_le_pow_right' (by norm_num) (by omega)
      have hmS : m ∈ Finset.Ico 1 (2 ^ K) := by
        apply Finset.mem_Ico.mpr
        refine ⟨?_, lt_of_lt_of_le (Finset.mem_Ico.mp hmBlock).2 ?_⟩
        · exact le_trans (Nat.one_le_pow k 2 (by norm_num)) (Finset.mem_Ico.mp hmBlock).1
        · exact hpowK
      have hnS : n ∈ Finset.Ico 1 (2 ^ K) := by
        apply Finset.mem_Ico.mpr
        refine ⟨?_, lt_of_lt_of_le (Finset.mem_Ico.mp hnBlock).2 ?_⟩
        · exact le_trans (Nat.one_le_pow l 2 (by norm_num)) (Finset.mem_Ico.mp hnBlock).1
        · exact hpowL
      exact ⟨⟨hmS, hnS⟩, by simp [g, hmk, hnk]⟩
  have hReindex :
      (∑ z ∈ S, f z.1 z.2) =
        ∑ kl ∈ T, ∑ z ∈ S.filter (fun z => g z = kl), f z.1 z.2 :=
    (Finset.sum_fiberwise_of_maps_to (g := g) (t := T) hmap
      (fun z => f z.1 z.2)).symm
  calc
    (∑ m ∈ Finset.Ico 1 (2 ^ K), ∑ n ∈ Finset.Ico 1 (2 ^ K), f m n) =
        ∑ z ∈ S, f z.1 z.2 := by rw [← Finset.sum_product']
    _ = ∑ kl ∈ T, ∑ z ∈ S.filter (fun z => g z = kl), f z.1 z.2 := hReindex
    _ = ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ∑ z ∈ S.filter (fun z => g z = (k, l)), f z.1 z.2 := by
        change (∑ kl ∈ Finset.range K ×ˢ Finset.range K,
          (fun k l => ∑ z ∈ S.filter (fun z => g z = (k, l)), f z.1 z.2)
            kl.1 kl.2) = _
        exact Finset.sum_product' (Finset.range K) (Finset.range K)
          (fun k l => ∑ z ∈ S.filter (fun z => g z = (k, l)), f z.1 z.2)
    _ = ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ∑ z ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1)) ×ˢ
            Finset.Ico (2 ^ l) (2 ^ (l + 1))), f z.1 z.2 := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        rw [hFiber k l hk hl]
    _ = ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
            ∑ n ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), f m n := by
        simp_rw [Finset.sum_product']

set_option maxHeartbeats 1000000 in
/-- The two factors of an unbalanced candidate pair and their dyadic lower
endpoints meet the Type II factor ranges. -/
theorem pair_box_ranges_core
    (x b bstar κ γ γ' : ℝ) (m p u U V : ℕ)
    (hx : 3 ≤ x) (hb : 0 < b) (hbstar : 0 < bstar)
    (hbstarSmall : bstar < 1 / 2) (hbstarEq : b = 3 * bstar)
    (hSlack : 5 ≤ x ^ (2 * bstar))
    (hγ : b ≤ γ) (hγ' : γ' ≤ 1 / 2 - κ) (hκ : 0 < κ)
    (hmBox : m ∈ Finset.Ico U (2 * U))
    (hpBox : p ∈ Finset.Ico V (2 * V))
    (hprod : m * p = 2 * u + 1)
    (hSupport : x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hp : Nat.Prime p) (hpLo : x ^ γ < (p : ℝ))
    (hpHi : (p : ℝ) ≤ x ^ γ') :
    x / 8 ≤ (U : ℝ) * (V : ℝ) ∧
      (U : ℝ) * (V : ℝ) ≤ 8 * x ∧
      x ^ bstar ≤ (U : ℝ) ∧ (U : ℝ) ≤ x ^ (1 - bstar) ∧
      x ^ bstar ≤ (V : ℝ) ∧ (V : ℝ) ≤ x ^ (1 - bstar) := by
  have hxpos : 0 < x := by linarith
  have hxle : 1 ≤ x := by linarith
  have hN : ((2 * u + 1 : ℕ) : ℝ) = (m : ℝ) * (p : ℝ) := by
    exact_mod_cast hprod.symm
  have hNlo : 2 * x ≤ (m : ℝ) * (p : ℝ) := by
    rw [← hN]
    push_cast
    nlinarith [hSupport.1]
  have hNhi : (m : ℝ) * (p : ℝ) ≤ 5 * x := by
    rw [← hN]
    push_cast
    nlinarith [hSupport.2, hx]
  have hNloCast : 2 * x ≤ ((2 * u + 1 : ℕ) : ℝ) := by rw [hN]; exact hNlo
  have hNhiCast : ((2 * u + 1 : ℕ) : ℝ) ≤ 5 * x := by rw [hN]; exact hNhi
  have hpCastLo : (x ^ b : ℝ) ≤ (p : ℝ) := by
    have hpow : x ^ b ≤ x ^ γ := Real.rpow_le_rpow_of_exponent_le hxle hγ
    exact le_trans hpow hpLo.le
  have hγ'half : γ' < 1 / 2 := lt_of_le_of_lt hγ'
    (by nlinarith [hκ])
  have hpowHalf : x ^ γ' ≤ x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hxle hγ'half.le
  have hpCastHi : (p : ℝ) ≤ x ^ (1 / 2 : ℝ) := le_trans hpHi hpowHalf
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hmNatLo : U ≤ m := (Finset.mem_Ico.mp hmBox).1
  have hmNatHi : m < 2 * U := (Finset.mem_Ico.mp hmBox).2
  have hpNatLo : V ≤ p := (Finset.mem_Ico.mp hpBox).1
  have hpNatHi : p < 2 * V := (Finset.mem_Ico.mp hpBox).2
  have hMreal : (m : ℝ) = ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) := by
    have hmul : (m : ℝ) * (p : ℝ) = ((2 * u + 1 : ℕ) : ℝ) := hN.symm
    have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    calc
      (m : ℝ) = ((m : ℝ) * (p : ℝ)) / (p : ℝ) := by field_simp [hpne]
      _ = _ := by rw [hmul]
  have hhalf : x / x ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
    calc
      x / x ^ (1 / 2 : ℝ) = x ^ ((1 : ℝ) - 1 / 2) := by
        simpa [Real.rpow_one] using (Real.rpow_sub hxpos (1 : ℝ) (1 / 2 : ℝ)).symm
      _ = x ^ (1 / 2 : ℝ) := by congr 1 <;> ring
  have hMlower : 2 * x ^ (1 / 2 : ℝ) ≤ (m : ℝ) := by
    have hdiv1 : 2 * x / x ^ (1 / 2 : ℝ) ≤ 2 * x / (p : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hp0 hpCastHi
    have hdiv2 : 2 * x / (p : ℝ) ≤ ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) :=
      div_le_div_of_nonneg_right hNloCast (le_of_lt hp0)
    calc
      2 * x ^ (1 / 2 : ℝ) = 2 * (x / x ^ (1 / 2 : ℝ)) := by rw [hhalf]
      _ = 2 * x / x ^ (1 / 2 : ℝ) := by ring
      _ ≤ 2 * x / (p : ℝ) := hdiv1
      _ ≤ ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) := hdiv2
      _ = (m : ℝ) := hMreal.symm
  have hbstarHalf : x ^ bstar ≤ x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hxle (by linarith [hbstarSmall])
  have hMstar : 2 * x ^ bstar ≤ (m : ℝ) := by nlinarith [hMlower, hbstarHalf]
  have hpowB : x ^ b = x ^ bstar * x ^ (2 * bstar) := by
    rw [hbstarEq, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hPstar : 2 * x ^ bstar ≤ (p : ℝ) := by
    rw [hpowB] at hpCastLo
    have hbstarNonneg : 0 ≤ x ^ bstar :=
      Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) bstar
    have hmul := mul_le_mul_of_nonneg_left hSlack hbstarNonneg
    calc
      2 * x ^ bstar ≤ 5 * x ^ bstar := by nlinarith [hbstarNonneg]
      _ ≤ x ^ bstar * x ^ (2 * bstar) := by nlinarith [hmul]
      _ ≤ (p : ℝ) := hpCastLo
  have hUstar : x ^ bstar ≤ (U : ℝ) := by
    have hmHiReal : (m : ℝ) < 2 * (U : ℝ) := by exact_mod_cast hmNatHi
    nlinarith [hMstar]
  have hVstar : x ^ bstar ≤ (V : ℝ) := by
    have hpHiReal : (p : ℝ) < 2 * (V : ℝ) := by exact_mod_cast hpNatHi
    nlinarith [hPstar]
  have hMupper : (m : ℝ) ≤ x ^ (1 - bstar) := by
    have hnum : ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) ≤ 5 * x / (p : ℝ) :=
      div_le_div_of_nonneg_right hNhiCast (le_of_lt hp0)
    have hden : 5 * x / (p : ℝ) ≤ 5 * x / x ^ b :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hxpos _) hpCastLo
    have hxdiv : x / x ^ b = x ^ (1 - b) := by
      simpa using (Real.rpow_sub hxpos (1 : ℝ) b).symm
    have hpowMul : x ^ (1 - bstar) = x ^ (1 - b) * x ^ (2 * bstar) := by
      rw [← Real.rpow_add hxpos, hbstarEq]
      congr 1
      ring
    rw [hMreal]
    calc
      ((2 * u + 1 : ℕ) : ℝ) / (p : ℝ) ≤ 5 * x / (p : ℝ) := hnum
      _ ≤ 5 * x / x ^ b := hden
      _ = 5 * x ^ (1 - b) := by
        calc
          5 * x / x ^ b = 5 * (x / x ^ b) := by ring
          _ = 5 * x ^ (1 - b) := by rw [hxdiv]
      _ ≤ x ^ (1 - bstar) := by
        rw [hpowMul]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hSlack
          (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) (1 - b))
  have hPupper : (p : ℝ) ≤ x ^ (1 - bstar) := by
    have hexp : (1 / 2 : ℝ) ≤ 1 - bstar := by linarith [hbstarSmall]
    exact le_trans hpCastHi (Real.rpow_le_rpow_of_exponent_le hxle hexp)
  have hUupper : (U : ℝ) ≤ x ^ (1 - bstar) :=
    le_trans (Nat.cast_le.mpr hmNatLo) hMupper
  have hVupper : (V : ℝ) ≤ x ^ (1 - bstar) :=
    le_trans (Nat.cast_le.mpr hpNatLo) hPupper
  have hUVupper : (U : ℝ) * (V : ℝ) ≤ 8 * x := by
    have hUm : (U : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hmNatLo
    have hVp : (V : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hpNatLo
    calc
      (U : ℝ) * (V : ℝ) ≤ (U : ℝ) * (p : ℝ) :=
        mul_le_mul_of_nonneg_left hVp (by positivity)
      _ ≤ (m : ℝ) * (p : ℝ) :=
        mul_le_mul_of_nonneg_right hUm (by positivity)
      _ ≤ 5 * x := hNhi
      _ ≤ 8 * x := mul_le_mul_of_nonneg_right
        (by norm_num : (5 : ℝ) ≤ 8) (le_trans (by norm_num : (0 : ℝ) ≤ 3) hx)
  have hUVlower : x / 8 ≤ (U : ℝ) * (V : ℝ) := by
    have hmU : (m : ℝ) < 2 * (U : ℝ) := by exact_mod_cast hmNatHi
    have hpV : (p : ℝ) < 2 * (V : ℝ) := by exact_mod_cast hpNatHi
    have hUpos : 0 < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
    have h₁ : (m : ℝ) * (p : ℝ) < 2 * (U : ℝ) * (p : ℝ) :=
      mul_lt_mul_of_pos_right hmU hp0
    have h₂ : 2 * (U : ℝ) * (p : ℝ) < 2 * (U : ℝ) * (2 * (V : ℝ)) :=
      mul_lt_mul_of_pos_left hpV (mul_pos (by norm_num) hUpos)
    have hprodLt : (m : ℝ) * (p : ℝ) < 4 * (U : ℝ) * (V : ℝ) := by
      calc
        _ < 2 * (U : ℝ) * (p : ℝ) := h₁
        _ < 2 * (U : ℝ) * (2 * (V : ℝ)) := h₂
        _ = 4 * (U : ℝ) * (V : ℝ) := by ring
    have hdivided : x / 2 < (U : ℝ) * (V : ℝ) := by
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      linarith [hNlo, hprodLt]
    have hxdiv : x / 8 ≤ x / 2 := by
      have hconst : (1 / 8 : ℝ) ≤ 1 / 2 := by norm_num
      calc
        x / 8 = (1 / 8 : ℝ) * x := by ring
        _ ≤ (1 / 2 : ℝ) * x := mul_le_mul_of_nonneg_right hconst hxpos.le
        _ = x / 2 := by ring
    exact le_trans hxdiv hdivided.le
  exact ⟨hUVlower, hUVupper, hUstar, hUupper, hVstar, hVupper⟩

/-- An interval of size `O(x)` fits inside a dyadic range with only `O(log x)`
blocks. -/
theorem exists_logarithmic_dyadic_cutoff (x : ℝ) (hx : 3 ≤ x) :
    ∃ K : ℕ, 5 * x < ((2 ^ K : ℕ) : ℝ) ∧
      (K : ℝ) ≤ (3 / Real.log 2) * Analytic.L x + 1 := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Analytic.L x := by
    dsimp [Analytic.L]
    exact Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := 3 / Real.log 2
  let K : ℕ := ⌈c * Analytic.L x⌉₊
  have hc : 0 < c := by dsimp [c]; positivity
  have hKlo : c * Analytic.L x ≤ (K : ℝ) := by
    exact Nat.le_ceil _
  have hKhi : (K : ℝ) < c * Analytic.L x + 1 := by
    dsimp [K]
    exact Nat.ceil_lt_add_one (le_of_lt (mul_pos hc hlogx))
  have hCoeff : Real.log 2 * c = 3 := by
    dsimp [c]
    field_simp [ne_of_gt hlog2]
  have hexp : 3 * Analytic.L x ≤ Real.log 2 * (K : ℝ) := by
    calc
      3 * Analytic.L x = (Real.log 2 * c) * Analytic.L x := by rw [hCoeff]
      _ = Real.log 2 * (c * Analytic.L x) := by ring
      _ ≤ Real.log 2 * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hKlo hlog2.le
  have hpowEq : ((2 ^ K : ℕ) : ℝ) = Real.exp (Real.log 2 * (K : ℝ)) := by
    calc
      ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K := by norm_cast
      _ = (2 : ℝ) ^ (K : ℝ) := by rw [Real.rpow_natCast]
      _ = Real.exp (Real.log 2 * (K : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hx3Eq : Real.exp (3 * Analytic.L x) = x ^ (3 : ℕ) := by
    have h := (Real.rpow_def_of_pos hxpos (3 : ℝ)).symm
    calc
      Real.exp (3 * Analytic.L x) = x ^ (3 : ℝ) := by
        simpa [Analytic.L, mul_comm] using h
      _ = x ^ (3 : ℕ) := Real.rpow_natCast x 3
  have hx3 : 5 * x < x ^ (3 : ℕ) := by
    have hxSq : 5 ≤ x ^ (2 : ℕ) := by nlinarith [hx]
    have hxMul : 5 * x ≤ x ^ 2 * x :=
      mul_le_mul_of_nonneg_right hxSq hxpos.le
    have hxStrict : 5 * x < x ^ 2 * x := by
      have hxSqStrict : 5 < x ^ 2 := by nlinarith [hx]
      nlinarith [mul_pos hxpos (sub_pos.mpr hxSqStrict)]
    simpa [pow_succ] using hxStrict
  have hpowLe : x ^ (3 : ℕ) ≤ ((2 ^ K : ℕ) : ℝ) := by
    rw [← hx3Eq, hpowEq]
    exact Real.exp_le_exp.mpr hexp
  refine ⟨K, ?_, ?_⟩
  · exact lt_of_lt_of_le hx3 hpowLe
  · exact le_of_lt hKhi

/-- Restricting a proxy discrepancy to the natural dyadic block leaves it
unchanged when its inclusive upper endpoint is the last integer below `2U`. -/
theorem restricted_proxyDifference_eq (I : FactorTest) (x S : ℝ) (U : ℕ)
    (hU : 0 < U) :
    restricted (U : ℝ)
        (proxyDifference I x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ)) =
      proxyDifference I x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ) := by
  funext n
  by_cases hbox : (U : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < 2 * (U : ℝ)
  · have hUle : U ≤ n := by exact_mod_cast hbox.1
    have hnlt : n < 2 * U := by exact_mod_cast hbox.2
    have hnhi : n ≤ 2 * U - 1 := by omega
    have hInt : (U : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ ((2 * U - 1 : ℕ) : ℝ) :=
      ⟨hbox.1, by exact_mod_cast hnhi⟩
    simp only [restricted, if_pos hbox, proxyDifference, if_pos hInt]
  · have hInt : ¬ ((U : ℝ) ≤ (n : ℝ) ∧
        (n : ℝ) ≤ ((2 * U - 1 : ℕ) : ℝ)) := by
      rintro ⟨hlo, hhi⟩
      have hUle : U ≤ n := by exact_mod_cast hlo
      have hnhi : n ≤ 2 * U - 1 := by exact_mod_cast hhi
      have hnlt : n < 2 * U := by omega
      exact hbox ⟨by exact_mod_cast hUle, by exact_mod_cast hnlt⟩
    simp only [restricted, if_neg hbox, proxyDifference, if_neg hInt]

/-- Prime-bin coefficient for a Type II factor variable. -/
def primeBinIndicator (x γ γ' : ℝ) (p : ℕ) : ℂ :=
  if p.Prime ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' then 1 else 0

/-- Real-valued Type II sum with the actual roughness test in the first
factor and the prime-bin test in the second. -/
def roughProxyErrorBox (D : BandData) (x : ℝ) (jstar : ℕ) (psi : ℝ → ℝ)
    (γ γ' S : ℝ) (U V : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico U (2 * U), ∑ p ∈ Finset.Ico V (2 * V),
    if Odd (m * p) ∧ 1 < m * p then
      D.weight x jstar ((m * p - 1) / 2) *
        psi (((m * p - 1) / 2 : ℕ) / x) *
          (test (.rough γ) x m - proxy (.rough γ) x S m) *
            (if p.Prime ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' then 1 else 0)
    else 0

/-- The complex Type II form with proxy-difference coefficients is exactly
the real finite sum over the corresponding natural dyadic boxes. -/
theorem typeIISum_proxyDifference_eq (D : BandData) (x : ℝ) (jstar : ℕ)
    (psi : ℝ → ℝ) (γ γ' S : ℝ) (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) :
    typeIISum D x jstar (U : ℝ) (V : ℝ) psi
      (proxyDifference (.rough γ) x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ))
      (primeBinIndicator x γ γ') =
        (roughProxyErrorBox D x jstar psi γ γ' S U V : ℂ) := by
  classical
  have hceilU : ⌈2 * (U : ℝ)⌉₊ = 2 * U := by
    calc
      ⌈2 * (U : ℝ)⌉₊ = ⌈((2 * U : ℕ) : ℝ)⌉₊ := by congr 1 <;> norm_cast
      _ = 2 * U := Nat.ceil_natCast _
  have hceilV : ⌈2 * (V : ℝ)⌉₊ = 2 * V := by
    calc
      ⌈2 * (V : ℝ)⌉₊ = ⌈((2 * V : ℕ) : ℝ)⌉₊ := by congr 1 <;> norm_cast
      _ = 2 * V := Nat.ceil_natCast _
  have hUbox : Finset.Ico ⌈(U : ℝ)⌉₊ ⌈2 * (U : ℝ)⌉₊ =
      Finset.Ico U (2 * U) := by rw [Nat.ceil_natCast, hceilU]
  have hVbox : Finset.Ico ⌈(V : ℝ)⌉₊ ⌈2 * (V : ℝ)⌉₊ =
      Finset.Ico V (2 * V) := by rw [Nat.ceil_natCast, hceilV]
  have hEach (m p : ℕ) (hm : m ∈ Finset.Ico U (2 * U)) :
      (if Odd (m * p) ∧ 1 < m * p then
        (D.weight x jstar ((m * p - 1) / 2) *
            psi (((m * p - 1) / 2 : ℕ) / x) : ℝ) *
          proxyDifference (.rough γ) x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ) m *
          primeBinIndicator x γ γ' p
       else 0) =
      ((if Odd (m * p) ∧ 1 < m * p then
          D.weight x jstar ((m * p - 1) / 2) *
            psi (((m * p - 1) / 2 : ℕ) / x) *
              (test (.rough γ) x m - proxy (.rough γ) x S m) *
                (if p.Prime ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' then 1 else 0)
        else 0 : ℝ) : ℂ) := by
    by_cases hprod : Odd (m * p) ∧ 1 < m * p
    · have hcoef : m ∈ Finset.Ico U (2 * U) →
          proxyDifference (.rough γ) x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ) m =
              ((test (.rough γ) x m - proxy (.rough γ) x S m : ℝ) : ℂ) := by
        intro hmem
        have hmU : U ≤ m := (Finset.mem_Ico.mp hmem).1
        have hmhi : m < 2 * U := (Finset.mem_Ico.mp hmem).2
        have hmReal : (U : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (U : ℝ) :=
          ⟨by exact_mod_cast hmU, by exact_mod_cast hmhi⟩
        have hmi : m ≤ 2 * U - 1 := by omega
        have hmInt : (U : ℝ) ≤ (m : ℝ) ∧
            (m : ℝ) ≤ ((2 * U - 1 : ℕ) : ℝ) :=
          ⟨hmReal.1, by exact_mod_cast hmi⟩
        simp [proxyDifference, hmReal, hmInt]
      have hRestr := hcoef hm
      rw [hRestr]
      by_cases hbin : p.Prime ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
      · simp [primeBinIndicator, hbin, hprod, Complex.ofReal_mul]
      · simp [primeBinIndicator, hbin, hprod, Complex.ofReal_mul]
    · simp [hprod]
  unfold typeIISum roughProxyErrorBox
  simp_rw [hUbox, hVbox, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro p hp
  exact hEach m p hm

/-- Apply the Type II hypothesis to an actual-minus-proxy roughness test
against primes in a fixed exponent bin. -/
theorem typeII_roughProxyErrorBox_bound
    (hII : TypeIIEstimate) (hp : ProxyInputs) (C : CandidateData)
    (hValid : C.bands.Valid) (hPsi : ContDiff ℝ ∞ C.psi)
    (hPsiSupport : Function.support C.psi ⊆ Set.Icc 1 2)
    (jstar : ℕ) (Dsave bstar b κ γ γ' : ℝ)
    (hDsave : 0 < Dsave) (hbstar : 0 < bstar)
    (hslot : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hγ : b ≤ γ) (hγlt : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ S : ℝ, 2 * B + 3 < S → ∀ᶠ x : ℝ in atTop,
        1 < x ∧ 1 ≤ Analytic.L x ∧ Analytic.W x ≤ x ^ γ ∧
        ∀ U V : ℕ,
          x / 8 ≤ (U : ℝ) * (V : ℝ) →
          (U : ℝ) * (V : ℝ) ≤ 8 * x →
          x ^ bstar ≤ (U : ℝ) → (U : ℝ) ≤ x ^ (1 - bstar) →
          x ^ bstar ≤ (V : ℝ) → (V : ℝ) ≤ x ^ (1 - bstar) →
          x ^ (b / 4) ≤ (U : ℝ) →
          ((2 * U - 1 : ℕ) : ℝ) ≤ x ^ (1 - b / 4) →
          |roughProxyErrorBox C.bands x jstar C.psi γ γ' S U V| ≤
            K * x * Analytic.L x ^ (-Dsave) := by
  obtain ⟨B, K, hB, hK, hTypeIIEvent⟩ :=
    hII C.bands hValid Dsave bstar 1 hDsave hbstar (by norm_num) jstar hslot
      C.psi hPsi hPsiSupport
  refine ⟨B, K, hB, hK, ?_⟩
  intro S hS
  have hProxyEvent := hp.discrepancy b κ B hb hκ hκsmall hB S hS
  have hWEvent := eventually_W_le_rpow γ (lt_of_lt_of_le hb hγ)
  have hLogEvent : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.L x := by
    simpa [Analytic.L] using Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hXEvent : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  filter_upwards [hTypeIIEvent, hProxyEvent, hWEvent, hLogEvent, hXEvent]
    with x hTypeII hProxy hW hL hx
  refine ⟨hx, hL, hW, ?_⟩
  intro U V hUVlo hUVhi hUlo hUhi hVlo hVhi hProxyLo hProxyHi
  have hx1 : 1 ≤ x := hx.le
  have hpow1 : 1 ≤ x ^ bstar := Real.one_le_rpow hx1 hbstar.le
  have hU1real : (1 : ℝ) ≤ (U : ℝ) := le_trans hpow1 hUlo
  have hV1real : (1 : ℝ) ≤ (V : ℝ) := le_trans hpow1 hVlo
  have hU1 : 1 ≤ U := by exact_mod_cast hU1real
  have hV1 : 1 ≤ V := by exact_mod_cast hV1real
  have hUpos : 0 < U := lt_of_lt_of_le Nat.zero_lt_one hU1
  have hVpos : 0 < V := lt_of_lt_of_le Nat.zero_lt_one hV1
  have hUpperCo : (U : ℝ) ≤ ((2 * U - 1 : ℕ) : ℝ) := by
    have hnat : U ≤ 2 * U - 1 := by omega
    exact_mod_cast hnat
  have hTest : TestAllowed b κ (.rough γ) := by
    change b ≤ γ ∧ γ ≤ 1 / 2 - κ
    exact ⟨hγ, le_trans hγlt.le hγ'⟩
  have hProxyData := hProxy (.rough γ) (U : ℝ) ((2 * U - 1 : ℕ) : ℝ)
    hTest hProxyLo hUpperCo hProxyHi
  rcases hProxyData with ⟨hDiscrepancy, hProxyBounds⟩
  have hPointProxy : ∀ n : ℕ, (U : ℝ) ≤ (n : ℝ) →
      (n : ℝ) ≤ ((2 * U - 1 : ℕ) : ℝ) →
      0 ≤ proxy (.rough γ) x S n ∧ proxy (.rough γ) x S n ≤ 1 := by
    intro n hnlo hnhi
    rcases hProxyBounds n hnlo hnhi with ⟨_, hnonneg, hle⟩
    exact ⟨hnonneg, hle⟩
  have hDeltaNorm := proxyDifference_norm_le_one (.rough γ) x S (U : ℝ)
    ((2 * U - 1 : ℕ) : ℝ) hPointProxy
  have hBetaNorm : ∀ n : ℕ, ‖primeBinIndicator x γ γ' n‖ ≤ 1 := by
    intro n
    by_cases hn : n.Prime ∧ x ^ γ < (n : ℝ) ∧ (n : ℝ) ≤ x ^ γ'
    · simp [primeBinIndicator, hn]
    · simp [primeBinIndicator, hn]
  have hLpow : 1 ≤ Analytic.L x ^ (1 : ℝ) := by simpa using hL
  have hCoeff : ∀ n : ℕ,
      ‖proxyDifference (.rough γ) x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ) n‖ ≤
          Analytic.L x ^ (1 : ℝ) ∧
        ‖primeBinIndicator x γ γ' n‖ ≤ Analytic.L x ^ (1 : ℝ) := by
    intro n
    exact ⟨le_trans (hDeltaNorm n) hLpow, le_trans (hBetaNorm n) hLpow⟩
  have hSupport : ∀ n : ℕ,
      proxyDifference (.rough γ) x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ) n ≠ 0 →
        Analytic.rough (Analytic.W x) n := by
    intro n hn
    exact roughProxyDifference_support x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ)
      γ n hW hn
  have hRestrictedDiscrepancy :
      Analytic.discrepancy x B
        (restricted (U : ℝ)
          (proxyDifference (.rough γ) x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ))) := by
    rw [restricted_proxyDifference_eq (.rough γ) x S U hUpos]
    exact hDiscrepancy
  have hTypeII := hTypeII (U : ℝ) (V : ℝ)
    (proxyDifference (.rough γ) x S (U : ℝ) ((2 * U - 1 : ℕ) : ℝ))
    (primeBinIndicator x γ γ') hUVlo hUVhi hUlo hUhi hVlo hVhi
    hCoeff hSupport hRestrictedDiscrepancy
  rw [typeIISum_proxyDifference_eq C.bands x jstar C.psi γ γ' S U V hUpos hVpos] at hTypeII
  simpa [Complex.norm_real] using hTypeII

/-- A uniformly bounded nonnegative factor can be pulled out of a weighted
finite sum. -/
theorem sum_weight_bounded_factor_le {α : Type*} [DecidableEq α]
    (s : Finset α) (w f : α → ℝ) (P : α → Prop) (Q : ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hf : ∀ a ∈ s, P a → 0 ≤ f a ∧ f a ≤ Q) :
    (∑ a ∈ s, if P a then w a * f a else 0) ≤
      Q * (∑ a ∈ s, if P a then w a else 0) := by
  classical
  calc
    (∑ a ∈ s, if P a then w a * f a else 0) ≤
        ∑ a ∈ s, if P a then Q * w a else 0 := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases hP : P a
          · rcases hf a ha hP with ⟨_, hfQ⟩
            simp [hP]
            nlinarith [mul_le_mul_of_nonneg_left hfQ (hw a ha)]
          · simp [hP]
    _ = Q * (∑ a ∈ s, if P a then w a else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hP : P a <;> simp [hP]

/-- Filtering by nonzero weight does not change a weighted finite sum. -/
theorem sum_indicator_ne_zero_weight_eq {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (P : α → Prop) :
    (∑ a ∈ s, if P a ∧ w a ≠ 0 then w a else 0) =
      ∑ a ∈ s, if P a then w a else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hP : P a
  · by_cases hw : w a = 0 <;> simp [hP, hw]
  · simp [hP]

/-- The least prime factor is no larger than any specified prime divisor. -/
theorem minFac_le_prime_divisor {n p : ℕ} (hp : Nat.Prime p) (hpdvd : p ∣ n) :
    n.minFac ≤ p :=
  Nat.minFac_le_of_dvd hp.two_le hpdvd

/-- For squarefree moduli, divisibility is equivalent to divisibility by each
prime factor. -/
theorem squarefree_dvd_iff_prime_factors_dvd {d n : ℕ}
    (hd : Squarefree d) :
    d ∣ n ↔ ∀ p ∈ d.primeFactors, p ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  constructor
  · intro h p hp
    exact dvd_trans (Nat.mem_primeFactors.mp hp).2.1 h
  · intro h
    rw [← Nat.prod_primeFactors_of_squarefree hd]
    apply (Nat.prod_primeFactors_dvd_iff (n := d) (k := n) hn).2
    intro p hp
    exact (Nat.mem_primeFactors_of_ne_zero hn).2
      ⟨Nat.prime_of_mem_primeFactors hp, h p hp⟩

/-- Euler's totient of a squarefree integer is the product of `p-1` over
its prime factors. -/
theorem totient_eq_prime_factor_predecessor_product {d : ℕ}
    (hd : Squarefree d) :
    Nat.totient d = ∏ p ∈ d.primeFactors, (p - 1) := by
  have hd0 : d ≠ 0 := hd.ne_zero
  rw [Nat.totient_eq_div_primeFactors_mul d,
    Nat.prod_primeFactors_of_squarefree hd]
  rw [Nat.div_self (Nat.pos_of_ne_zero hd0), one_mul]

/-- Reciprocal prime-factor densities multiply to the reciprocal totient on
squarefree moduli. -/
theorem prime_factor_density_product {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1)) =
      1 / (Nat.totient d : ℝ) := by
  rw [totient_eq_prime_factor_predecessor_product hd]
  simp only [one_div]
  rw [Finset.prod_inv_distrib, Nat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hpge : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
  norm_cast

/-- Candidate weights as a finite sieve problem for odd prime divisors of
`2u+1`. -/
def candidateSieveData (C : CandidateData) (x : ℝ) (jstar : ℕ) (y : ℝ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) : SieveData ℕ where
  objects := Finset.Icc 1 ⌊2 * x⌋₊
  weight := C.weighted x jstar
  primes := (primesUpTo y).erase 2
  bad := fun p u => p ∣ 2 * u + 1
  X := C.mass x jstar
  density := fun p => 1 / ((p : ℝ) - 1)
  nonneg := by
    intro u hu
    exact hweight u
  prime := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
  X_nonneg := hmass

/-- Candidate mass surviving divisibility by the odd primes at most `y`. -/
def candidateSiftedMass (C : CandidateData) (x : ℝ) (jstar : ℕ) (y : ℝ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
    if ∀ p ∈ (primesUpTo y).erase 2, ¬ p ∣ 2 * u + 1 then
      C.weighted x jstar u else 0

/-- The abstract sieve's sifted mass unfolds to the candidate survivor sum. -/
theorem candidateSieve_sifted_eq (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) :
    (candidateSieveData C x jstar y hweight hmass).sifted =
      candidateSiftedMass C x jstar y := by
  simp [SieveData.sifted, candidateSieveData, candidateSiftedMass]

/-- The candidate sieve has the expected Euler product. -/
theorem candidateSieve_product (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) :
    (candidateSieveData C x jstar y hweight hmass).product = shiftedSieveProduct y := by
  simp [SieveData.product, candidateSieveData, shiftedSieveProduct, one_div]

/-- The sieve density of a squarefree modulus is exactly the Type I main term. -/
theorem candidateSieve_g (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) {d : ℕ} (hd : Squarefree d) :
    (candidateSieveData C x jstar y hweight hmass).g d =
      1 / (Nat.totient d : ℝ) := by
  simpa [SieveData.g, candidateSieveData] using prime_factor_density_product hd

/-- The local sieve monomial detects divisibility by a squarefree modulus. -/
theorem candidateSieve_monomial (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) {d u : ℕ} (hd : Squarefree d) :
    (candidateSieveData C x jstar y hweight hmass).monomial d u =
      if d ∣ 2 * u + 1 then 1 else 0 := by
  simp only [SieveData.monomial, candidateSieveData]
  simpa only [← squarefree_dvd_iff_prime_factors_dvd (d := d) (n := 2 * u + 1) hd]

/-- Summing an indicator over a finite set is the corresponding filtered sum. -/
theorem sum_mul_indicator_eq_filter {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (p : α → Prop) :
    (∑ a ∈ s, w a * (if p a then 1 else 0)) =
      ∑ a ∈ (s.filter p), w a := by
  classical
  simp [Finset.sum_filter]

/-- On squarefree moduli, the candidate sieve remainder is the Type I
remainder from the blueprint. -/
theorem candidateSieve_remainder (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) {d : ℕ} (hd : Squarefree d) :
    (candidateSieveData C x jstar y hweight hmass).remainder d =
      C.remainder x jstar d := by
  classical
  rw [SieveData.remainder, CandidateData.remainder]
  simp_rw [candidateSieve_monomial C x jstar y hweight hmass hd,
    candidateSieve_g C x jstar y hweight hmass hd]
  simp only [candidateSieveData]
  simp_rw [Finset.sum_filter]
  simp [mul_ite, div_eq_mul_inv]

/-- Sieve data for the candidate weight restricted to multiples of a fixed
prime divisor of `2u+1`. -/
def primeDivisorSieveData (C : CandidateData) (x : ℝ) (jstar p : ℕ) (y : ℝ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) : SieveData ℕ where
  objects := Finset.Icc 1 ⌊2 * x⌋₊
  weight := fun u => if p ∣ 2 * u + 1 then C.weighted x jstar u else 0
  primes := (primesUpTo y).erase 2
  bad := fun q u => q ∣ 2 * u + 1
  X := C.mass x jstar / (Nat.totient p : ℝ)
  density := fun q => 1 / ((q : ℝ) - 1)
  nonneg := by
    intro u hu
    by_cases hpdiv : p ∣ 2 * u + 1 <;> simp [hpdiv, hweight u]
  prime := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).2
  X_nonneg := by
    exact div_nonneg hmass (Nat.cast_nonneg _)

/-- Squarefree moduli supported on the odd primes up to the sieve cutoff. -/
def smallSieveModuli (y D : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊D⌋₊).filter
    (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2)

/-- The fixed-prime sieve and ordinary candidate sieve use the same modulus
set. -/
theorem primeDivisorSieve_products (C : CandidateData) (x : ℝ) (jstar p : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (D : ℝ) :
    (primeDivisorSieveData C x jstar p y hweight hmass).products D =
      smallSieveModuli y D := by
  rfl

/-- The fixed-prime sieve has the same Euler product as the ordinary odd
prime sieve. -/
theorem primeDivisorSieve_product (C : CandidateData) (x : ℝ) (jstar p : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) :
    (primeDivisorSieveData C x jstar p y hweight hmass).product =
      shiftedSieveProduct y := by
  simp [SieveData.product, primeDivisorSieveData, shiftedSieveProduct, one_div]

/-- Weighted values surviving the small-prime sieve and divisible by `p`. -/
def primeDivisorSiftedMass (C : CandidateData) (x : ℝ) (jstar p : ℕ) (y : ℝ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
    if p ∣ 2 * u + 1 ∧ ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1 then
      C.weighted x jstar u else 0

/-- Fixed-prime survivor mass weighted by a proxy for the cofactor. -/
def primeDivisorProxySiftedMass (C : CandidateData) (x : ℝ) (jstar p : ℕ)
    (y γ S : ℝ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
    if (p ∣ 2 * u + 1 ∧
        (∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1)) ∧
          C.weighted x jstar u ≠ 0 then
      C.weighted x jstar u *
        proxy (.rough γ) x S ((2 * u + 1) / p) else 0

/-- The abstract `p`-divisor sieve survivor sum has the declared meaning. -/
theorem primeDivisorSieve_sifted_eq (C : CandidateData) (x : ℝ)
    (jstar p : ℕ) (y : ℝ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) :
    (primeDivisorSieveData C x jstar p y hweight hmass).sifted =
      primeDivisorSiftedMass C x jstar p y := by
  classical
  simp only [SieveData.sifted, primeDivisorSieveData, primeDivisorSiftedMass]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hpdiv : p ∣ 2 * u + 1
  · by_cases hrough : ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1 <;>
      simp [hpdiv, hrough]
  · simp [hpdiv]

/-- A pointwise upper bound for the cofactor proxy pulls out of the
fixed-prime survivor mass. -/
theorem primeDivisorProxySiftedMass_sum_le
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (y γ S Q : ℝ) (P : Finset ℕ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hProxy : ∀ p ∈ P, ∀ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
      p ∣ 2 * u + 1 →
      (∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1) →
      C.weighted x jstar u ≠ 0 →
      0 ≤ proxy (.rough γ) x S ((2 * u + 1) / p) ∧
        proxy (.rough γ) x S ((2 * u + 1) / p) ≤ Q) :
    (∑ p ∈ P, primeDivisorProxySiftedMass C x jstar p y γ S) ≤
      Q * (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) := by
  classical
  have hEach (p : ℕ) (hp : p ∈ P) :
      primeDivisorProxySiftedMass C x jstar p y γ S ≤
        Q * primeDivisorSiftedMass C x jstar p y := by
    have hUpper :
        primeDivisorProxySiftedMass C x jstar p y γ S ≤
          Q * (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
            if (p ∣ 2 * u + 1 ∧
                (∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1)) ∧
                  C.weighted x jstar u ≠ 0 then C.weighted x jstar u else 0) := by
      unfold primeDivisorProxySiftedMass
      simpa using sum_weight_bounded_factor_le
        (Finset.Icc 1 ⌊2 * x⌋₊)
        (C.weighted x jstar)
        (fun u => proxy (.rough γ) x S ((2 * u + 1) / p))
        (fun u => (p ∣ 2 * u + 1 ∧
          (∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1)) ∧
            C.weighted x jstar u ≠ 0)
        Q (by intro u hu; exact hweight u) (by
          intro u hu hsurv
          exact hProxy p hp u hu hsurv.1.1 hsurv.1.2 hsurv.2)
    have hweightSum :
        (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if (p ∣ 2 * u + 1 ∧
              (∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1)) ∧
                C.weighted x jstar u ≠ 0 then C.weighted x jstar u else 0) =
          primeDivisorSiftedMass C x jstar p y := by
      unfold primeDivisorSiftedMass
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hdiv : p ∣ 2 * u + 1
      · by_cases hrough : ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1
        · have hP : p ∣ 2 * u + 1 ∧
              ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1 := ⟨hdiv, hrough⟩
          by_cases hw : C.weighted x jstar u = 0
          · have hleft : ¬ ((p ∣ 2 * u + 1 ∧
                ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1) ∧
                  C.weighted x jstar u ≠ 0) := by
              intro h
              exact h.2 hw
            rw [if_neg hleft, if_pos hP]
            simp [hw]
          · rw [if_pos ⟨hP, hw⟩, if_pos hP]
        · have hP : ¬ (p ∣ 2 * u + 1 ∧
              ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1) := by
            rintro ⟨_, hsurv⟩
            exact hrough hsurv
          have hleft : ¬ ((p ∣ 2 * u + 1 ∧
              ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1) ∧
                C.weighted x jstar u ≠ 0) := by
            intro h
            exact hP h.1
          rw [if_neg hleft, if_neg hP]
      · have hP : ¬ (p ∣ 2 * u + 1 ∧
            ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1) := by
          rintro ⟨hdiv', _⟩
          exact hdiv hdiv'
        have hleft : ¬ ((p ∣ 2 * u + 1 ∧
            ∀ q ∈ (primesUpTo y).erase 2, ¬ q ∣ 2 * u + 1) ∧
              C.weighted x jstar u ≠ 0) := by
          intro h
          exact hP h.1
        rw [if_neg hleft, if_neg hP]
    rw [hweightSum] at hUpper
    exact hUpper
  calc
    (∑ p ∈ P, primeDivisorProxySiftedMass C x jstar p y γ S) ≤
        ∑ p ∈ P, Q * primeDivisorSiftedMass C x jstar p y := by
          apply Finset.sum_le_sum
          intro p hp
          exact hEach p hp
    _ = Q * (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) := by
      rw [← Finset.mul_sum]

/-- Apply the rough-bin density bound to every supported cofactor and sum the
result over all large prime divisors in the bin. -/
theorem primeBinProxySiftedMass_sum_le
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (P : Finset ℕ)
    (γ γ' S Q : ℝ) (hX : 1 < x) (hW : 1 ≤ Analytic.W x)
    (hγ : 0 < γ) (hγ'pos : 0 < γ')
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hpPrime : ∀ p ∈ P, Nat.Prime p)
    (hpBin : ∀ p ∈ P, x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ')
    (hDensity : ∀ (m n u : ℕ), m * n = 2 * u + 1 →
      x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
      γ < Real.log (n : ℝ) / Analytic.L x →
        Real.log (n : ℝ) / Analytic.L x ≤ γ' →
      proxyConstant (.rough γ) x S m ≤ Q) :
    (∑ p ∈ P, primeDivisorProxySiftedMass C x jstar p
      (Analytic.W x) γ S) ≤
      Q * (∑ p ∈ P, primeDivisorSiftedMass C x jstar p (Analytic.W x)) := by
  apply primeDivisorProxySiftedMass_sum_le C x jstar (Analytic.W x) γ S Q P
    hweight
  intro p hp u hu hdiv hSurv hweightNe
  have hBounds := hSupport u hweightNe
  have hBin := hpBin p hp
  have hExponent := log_factor_mem_exponent_bin x (p : ℝ) γ γ' hX
    hγ hγ'pos hBin.1 hBin.2
  have hrel : ((2 * u + 1) / p) * p = 2 * u + 1 := Nat.div_mul_cancel hdiv
  have hConst := hDensity ((2 * u + 1) / p) p u hrel hBounds.1 hBounds.2
    hExponent.1 hExponent.2
  exact (proxy_cofactor_bound_from_sieve x S γ Q u p hW hdiv
    (hpPrime p hp) hSurv hConst)

/-- A supported cofactor in a fixed prime bin satisfies the ProxyInputs
density bound pointwise. -/
theorem proxyBinCofactorPointwiseBound
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (γ γ' S Q : ℝ)
    (u p : ℕ) (hx : 1 < x) (hW : 1 ≤ Analytic.W x)
    (hγ : 0 < γ) (hγ' : 0 < γ')
    (hSupport : C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hweight : C.weighted x jstar u ≠ 0)
    (hp : Nat.Prime p) (hpLo : x ^ γ < (p : ℝ)) (hpHi : (p : ℝ) ≤ x ^ γ')
    (hdiv : p ∣ 2 * u + 1)
    (hSurv : ∀ q ∈ (primesUpTo (Analytic.W x)).erase 2,
      ¬ q ∣ 2 * u + 1)
    (hDensity : ∀ m n u : ℕ, m * n = 2 * u + 1 →
      x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
      γ < Real.log (n : ℝ) / Analytic.L x →
        Real.log (n : ℝ) / Analytic.L x ≤ γ' →
      proxyConstant (.rough γ) x S m ≤ Q) :
    0 ≤ proxy (.rough γ) x S ((2 * u + 1) / p) ∧
      proxy (.rough γ) x S ((2 * u + 1) / p) ≤ Q := by
  have hSupport' := hSupport hweight
  have hExponent := log_factor_mem_exponent_bin x (p : ℝ) γ γ' hx hγ hγ' hpLo hpHi
  have hrel : ((2 * u + 1) / p) * p = 2 * u + 1 := Nat.div_mul_cancel hdiv
  have hConst := hDensity ((2 * u + 1) / p) p u hrel hSupport'.1 hSupport'.2
    hExponent.1 hExponent.2
  exact proxy_cofactor_bound_from_sieve x S γ Q u p hW hdiv hp hSurv hConst

/-- Squarefree local density for the fixed-prime sieve. -/
theorem primeDivisorSieve_g (C : CandidateData) (x : ℝ) (jstar p : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) {d : ℕ} (hd : Squarefree d) :
    (primeDivisorSieveData C x jstar p y hweight hmass).g d =
      1 / (Nat.totient d : ℝ) := by
  simpa [SieveData.g, primeDivisorSieveData] using prime_factor_density_product hd

/-- The fixed-prime sieve monomial detects squarefree divisibility. -/
theorem primeDivisorSieve_monomial (C : CandidateData) (x : ℝ) (jstar p : ℕ)
    (y : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) {d u : ℕ} (hd : Squarefree d) :
    (primeDivisorSieveData C x jstar p y hweight hmass).monomial d u =
      if d ∣ 2 * u + 1 then 1 else 0 := by
  simp only [SieveData.monomial, primeDivisorSieveData]
  simpa only [← squarefree_dvd_iff_prime_factors_dvd (d := d) (n := 2 * u + 1) hd]

/-- A prime above the sieve cutoff is coprime to every sieve modulus. -/
theorem primeDivisorSieve_coprime (C : CandidateData) (x : ℝ) (jstar p : ℕ)
    (y : ℝ) (hp : Nat.Prime p) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (hY : 1 < y) {d : ℕ} (hd : Squarefree d)
    (hsubset : d.primeFactors ⊆
      (primeDivisorSieveData C x jstar p y hweight hmass).primes)
    (hpy : y < (p : ℝ)) : Nat.Coprime p d := by
  have hpnotd : ¬ p ∣ d := by
    intro hpd
    have hdne : d ≠ 0 := hd.ne_zero
    have hpmem : p ∈ d.primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero hdne).2 ⟨hp, hpd⟩
    have hpSieve := hsubset hpmem
    have hpUp := (Finset.mem_erase.mp hpSieve).2
    have hpBase := Finset.mem_filter.mp hpUp
    have hpFloor : p ≤ ⌊y⌋₊ := (Finset.mem_Icc.mp hpBase.1).2
    have hpLe : (p : ℝ) ≤ y := le_trans (Nat.cast_le.mpr hpFloor)
      (Nat.floor_le (le_of_lt (lt_trans (by norm_num) hY)))
    exact (not_le_of_gt hpy) hpLe
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpnotd

/-- The fixed-prime sieve has the Type I main term at modulus `p*d`. -/
theorem primeDivisorSieve_main_eq (C : CandidateData) (x : ℝ) (jstar p : ℕ)
    (y : ℝ) (hp : Nat.Prime p) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (hY : 1 < y) {d : ℕ} (hd : Squarefree d)
    (hsubset : d.primeFactors ⊆
      (primeDivisorSieveData C x jstar p y hweight hmass).primes)
    (hpy : y < (p : ℝ)) :
    (primeDivisorSieveData C x jstar p y hweight hmass).X *
        (primeDivisorSieveData C x jstar p y hweight hmass).g d =
      C.mass x jstar / (Nat.totient (p * d) : ℝ) := by
  have hcop := primeDivisorSieve_coprime C x jstar p y hp hweight hmass hY hd hsubset hpy
  have hφp : 0 < Nat.totient p := Nat.totient_pos.mpr hp.pos
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hφd : 0 < Nat.totient d := Nat.totient_pos.mpr hdpos
  have hφmul : (Nat.totient (p * d) : ℝ) =
      (Nat.totient p : ℝ) * (Nat.totient d : ℝ) := by
    exact_mod_cast Nat.totient_mul hcop
  rw [primeDivisorSieve_g C x jstar p y hweight hmass hd, hφmul]
  simp [primeDivisorSieveData]
  field_simp [ne_of_gt hφp, ne_of_gt hφd]

/-- The fixed-prime sieve remainder is the Type I remainder at `p*d`. -/
theorem primeDivisorSieve_remainder (C : CandidateData) (x : ℝ) (jstar p : ℕ)
    (y : ℝ) (hp : Nat.Prime p) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (hY : 1 < y) {d : ℕ} (hd : Squarefree d)
    (hsubset : d.primeFactors ⊆
      (primeDivisorSieveData C x jstar p y hweight hmass).primes)
    (hpy : y < (p : ℝ)) :
    (primeDivisorSieveData C x jstar p y hweight hmass).remainder d =
      C.remainder x jstar (p * d) := by
  classical
  let S := primeDivisorSieveData C x jstar p y hweight hmass
  have hcop := primeDivisorSieve_coprime C x jstar p y hp hweight hmass hY hd hsubset hpy
  have hdiviff {u : ℕ} :
      p * d ∣ 2 * u + 1 ↔ p ∣ 2 * u + 1 ∧ d ∣ 2 * u + 1 := by
    constructor
    · intro h
      exact ⟨dvd_trans (dvd_mul_of_dvd_left dvd_rfl d) h,
        dvd_trans (dvd_mul_of_dvd_right dvd_rfl p) h⟩
    · rintro ⟨hpu, hdu⟩
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpu hdu
  have hsum :
      (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, S.weight u * S.monomial d u) =
        ∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => p * d ∣ 2 * u + 1),
          C.weighted x jstar u := by
    have hmon (u : ℕ) : S.monomial d u = if d ∣ 2 * u + 1 then 1 else 0 := by
      simpa [S] using primeDivisorSieve_monomial C x jstar p y hweight hmass hd
    simp_rw [hmon]
    simp only [S, primeDivisorSieveData]
    have hterm (u : ℕ) :
        (if p ∣ 2 * u + 1 then C.weighted x jstar u else 0) *
            (if d ∣ 2 * u + 1 then 1 else 0) =
          if p * d ∣ 2 * u + 1 then C.weighted x jstar u else 0 := by
      by_cases hpdiv : p ∣ 2 * u + 1
      · by_cases hddiv : d ∣ 2 * u + 1
        · have hpd : p * d ∣ 2 * u + 1 := hdiviff.mpr ⟨hpdiv, hddiv⟩
          simp [hpdiv, hddiv, hpd]
        · have hpd : ¬ p * d ∣ 2 * u + 1 := fun h => hddiv (hdiviff.mp h).2
          simp [hpdiv, hddiv, hpd]
      · have hpd : ¬ p * d ∣ 2 * u + 1 := fun h => hpdiv (hdiviff.mp h).1
        by_cases hddiv : d ∣ 2 * u + 1 <;> simp [hpdiv, hddiv, hpd]
    simp_rw [hterm]
    simp [Finset.sum_filter]
  have hmain := primeDivisorSieve_main_eq C x jstar p y hp hweight hmass hY hd hsubset hpy
  rw [SieveData.remainder, CandidateData.remainder]
  change (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, S.weight u * S.monomial d u) -
      S.X * S.g d =
    (∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => p * d ∣ 2 * u + 1),
      C.weighted x jstar u) - C.mass x jstar / Nat.totient (p * d)
  rw [hsum, hmain]

/-- Remainders indexed by a large prime times a small sieve modulus map
injectively into the Type I modulus set. -/
theorem prime_sieve_remainders_le_typeI
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (θ W : ℝ)
    (P D : Finset ℕ) (hX : 0 ≤ x)
    (hpPrime : ∀ p ∈ P, Nat.Prime p)
    (hpLarge : ∀ p ∈ P, W < (p : ℝ))
    (hdNe : ∀ d ∈ D, d ≠ 0)
    (hdPrimeBound : ∀ d ∈ D, ∀ q ∈ d.primeFactors, (q : ℝ) ≤ W)
    (hPair : ∀ p ∈ P, ∀ d ∈ D, Odd (p * d) ∧ Squarefree (p * d) ∧
      (p * d : ℝ) ≤ x ^ θ) :
    (∑ p ∈ P, ∑ d ∈ D, |C.remainder x jstar (p * d)|) ≤
      ∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun e => Odd e ∧ Squarefree e)),
        |C.remainder x jstar e| := by
  classical
  let S := P ×ˢ D
  let f : ℕ × ℕ → ℕ := fun z => z.1 * z.2
  have hinj : ∀ z₁ ∈ S, ∀ z₂ ∈ S, f z₁ = f z₂ → z₁ = z₂ := by
    intro ⟨p, d⟩ hz₁ ⟨q, e⟩ hz₂ heq
    rcases Finset.mem_product.mp hz₁ with ⟨hpP, hdD⟩
    rcases Finset.mem_product.mp hz₂ with ⟨hqP, heD⟩
    have hp := hpPrime p hpP
    have hq := hpPrime q hqP
    have hprod : p * d = q * e := by simpa [f] using heq
    have hpdvd : p ∣ q * e := by
      rw [← hprod]
      exact dvd_mul_right p d
    rcases hp.dvd_mul.mp hpdvd with hpq | hpe
    · have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
      subst q
      have hdeq : d = e := Nat.mul_left_cancel hp.pos heq
      subst e
      rfl
    · have heNe : e ≠ 0 := hdNe e heD
      have hpmem : p ∈ e.primeFactors :=
        (Nat.mem_primeFactors_of_ne_zero heNe).2 ⟨hp, hpe⟩
      have hpLE : (p : ℝ) ≤ W := hdPrimeBound e heD p hpmem
      exact False.elim (not_le_of_gt (hpLarge p hpP) hpLE)
  have hImageSum :
      (∑ z ∈ S, |C.remainder x jstar (f z)|) =
        ∑ e ∈ S.image f, |C.remainder x jstar e| := by
    refine Finset.sum_bij (fun z _ => f z) ?_ ?_ ?_ ?_
    · intro z hz
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      exact hinj z₁ hz₁ z₂ hz₂ heq
    · intro e he
      rcases Finset.mem_image.mp he with ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · intro z hz
      rfl
  have hImageSubset : S.image f ⊆
      (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun e => Odd e ∧ Squarefree e) := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨⟨p, d⟩, hz, rfl⟩
    rcases Finset.mem_product.mp hz with ⟨hpP, hdD⟩
    rcases hPair p hpP d hdD with ⟨hodd, hSq, hup⟩
    have hfloor : p * d ≤ ⌊x ^ θ⌋₊ := by
      apply (Nat.le_floor_iff (Real.rpow_nonneg hX θ)).2
      simpa only [Nat.cast_mul] using hup
    have hpos : 1 ≤ p * d := by
      have hpPos := (hpPrime p hpP).pos
      have hdPos := Nat.pos_of_ne_zero (hdNe d hdD)
      exact (Nat.one_le_iff_ne_zero).2 (Nat.mul_ne_zero hpPos.ne' hdPos.ne')
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpos, hfloor⟩, hodd, hSq⟩
  have hImageLe :
      (∑ e ∈ S.image f, |C.remainder x jstar e|) ≤
        ∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun e => Odd e ∧ Squarefree e)),
          |C.remainder x jstar e| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hImageSubset
    intro e he hnot
    positivity
  rw [← Finset.sum_product']
  exact hImageSum.le.trans hImageLe

/-- Filtering the larger prime interval by its lower endpoint recovers the
smaller prime interval. -/
theorem primesUpTo_filter_le_eq (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (primesUpTo b).filter (fun p : ℕ => (p : ℝ) ≤ a) = primesUpTo a := by
  classical
  ext p
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hlo, hhi⟩, hp⟩, hpa⟩
    exact ⟨⟨hlo, (Nat.le_floor_iff ha).2 hpa⟩, hp⟩
  · rintro ⟨⟨hlo, hfloor⟩, hp⟩
    refine ⟨⟨⟨hlo, le_trans hfloor (Nat.floor_mono hab)⟩, hp⟩,
      le_trans (Nat.cast_le.mpr hfloor) (Nat.floor_le ha)⟩

/-- Reciprocal primes on an interval are the difference of the two initial
reciprocal sums. -/
theorem prime_reciprocal_interval_eq_diff (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ (primesUpTo b).filter (fun p : ℕ => a < (p : ℝ)), 1 / (p : ℝ)) =
      (∑ p ∈ primesUpTo b, 1 / (p : ℝ)) -
        (∑ p ∈ primesUpTo a, 1 / (p : ℝ)) := by
  classical
  let s := primesUpTo b
  have hbelow : s.filter (fun p : ℕ => (p : ℝ) ≤ a) = primesUpTo a := by
    simpa [s] using primesUpTo_filter_le_eq a b ha hab
  have hnot : s.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ a)) =
      s.filter (fun p : ℕ => a < (p : ℝ)) := by
    ext p
    simp
  have hsplit :
      (∑ p ∈ s.filter (fun p : ℕ => (p : ℝ) ≤ a), 1 / (p : ℝ)) +
          (∑ p ∈ s.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ a)), 1 / (p : ℝ)) =
        ∑ p ∈ s, 1 / (p : ℝ) :=
    Finset.sum_filter_add_sum_filter_not s (fun p : ℕ => (p : ℝ) ≤ a)
      (fun p => 1 / (p : ℝ))
  rw [hbelow, hnot] at hsplit
  linarith

/-- Prime counting function for the candidate prime set. -/
def primeCount (y : ℝ) : ℝ := (primesUpTo y).card

/-- Abel summation rewrites reciprocal prime mass on an interval in terms of
the unweighted prime counting function. -/
theorem prime_reciprocal_interval_abel (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ (primesUpTo b).filter (fun p : ℕ => a < (p : ℝ)), 1 / (p : ℝ)) =
      (primeCount b) / b - (primeCount a) / a -
        ∫ t : ℝ in a..b, (-(t ^ 2)⁻¹) * primeCount t := by
  classical
  let c : ℕ → ℝ := fun n => if n.Prime then 1 else 0
  let f : ℝ → ℝ := fun t => t⁻¹
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hfDiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t := by
    intro t ht
    apply (differentiableAt_inv_iff).2
    exact ne_of_gt (lt_of_lt_of_le hapos ht.1)
  have hDerivCont : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.uIcc a b) := by
    have hsq : ContinuousOn (fun t : ℝ => t ^ 2) (Set.uIcc a b) := by fun_prop
    have hsqne : ∀ t ∈ Set.uIcc a b, t ^ 2 ≠ 0 := by
      intro t ht
      have ht' : a ≤ t ∧ t ≤ b := by simpa [Set.uIcc_of_le hab] using ht
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hapos ht'.1))
    exact (hsq.inv₀ hsqne).neg
  have hDerivContIcc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc a b) := by
    simpa [Set.uIcc_of_le hab] using hDerivCont
  have hfInt : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b) MeasureTheory.volume := by
    have hDerivEq : deriv f = fun t : ℝ => -(t ^ 2)⁻¹ := by
      funext t
      simp [f, deriv_inv]
    rw [hDerivEq]
    exact hDerivContIcc.integrableOn_Icc
  have hprimeFilter (t : ℝ) (ht : 2 ≤ t) :
      (Finset.Icc 0 ⌊t⌋₊).filter Nat.Prime = primesUpTo t := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, primesUpTo]
    constructor
    · rintro ⟨⟨_, hpFloor⟩, hp⟩
      exact ⟨⟨hp.one_le, hpFloor⟩, hp⟩
    · rintro ⟨⟨hpOne, hpFloor⟩, hp⟩
      exact ⟨⟨Nat.zero_le p, hpFloor⟩, hp⟩
  have hprefix (t : ℝ) (ht : 2 ≤ t) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = primeCount t := by
    have hsum := sum_mul_indicator_eq_filter (Finset.Icc 0 ⌊t⌋₊)
      (fun _ : ℕ => (1 : ℝ)) Nat.Prime
    have hsum' : (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        ∑ n ∈ (Finset.Icc 0 ⌊t⌋₊).filter Nat.Prime, 1 := by
      simpa [c, one_mul] using hsum
    rw [hprimeFilter t ht] at hsum'
    simpa [primeCount] using hsum'
  have hintervalSet :
      (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime =
        (primesUpTo b).filter (fun p : ℕ => a < (p : ℝ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, primesUpTo, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      have hreal : a < (p : ℝ) := (Nat.floor_lt' hp.ne_zero).mp hlo
      exact ⟨⟨⟨hp.one_le, hhi⟩, hp⟩, hreal⟩
    · rintro ⟨⟨⟨hpOne, hfloor⟩, hp⟩, hreal⟩
      have hlow : ⌊a⌋₊ < p := (Nat.floor_lt' hp.ne_zero).mpr hreal
      exact ⟨⟨hlow, hfloor⟩, hp⟩
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha0 hab hfDiff hfInt
  have hsumPrime :
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
        ∑ p ∈ (primesUpTo b).filter (fun p : ℕ => a < (p : ℝ)), 1 / (p : ℝ) := by
    calc
      _ = ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
        simp [c, f, Finset.sum_filter, mul_ite]
      _ = _ := by rw [hintervalSet]
  have hprefixA := hprefix a ha
  have hprefixB := hprefix b (le_trans ha hab)
  have hprefixT : ∀ t ∈ Set.Ioc a b,
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = primeCount t := by
    intro t ht
    exact hprefix t (le_trans ha (le_of_lt ht.1))
  have hIntPrefix :
      (∫ t : ℝ in Set.Ioc a b, deriv f t *
        (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)) =
      (∫ t : ℝ in Set.Ioc a b, deriv f t * primeCount t) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hprefixT t ht]
  rw [hsumPrime, hprefixA, hprefixB] at hAbel
  rw [hIntPrefix] at hAbel
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  simpa [f, deriv_inv, div_eq_mul_inv, mul_comm] using hAbel

/-- The progressions input supplies a prime-counting estimate at every fixed
logarithmic power. -/
theorem eventually_prime_count_li (hc : ClassicalInputs) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ y : ℝ in atTop,
      |(primesUpTo y).card - li y| ≤ K * y * Real.log y ^ (-A) := by
  obtain ⟨K, hK, hProgressions⟩ := hc.progressions A 1 hA (by norm_num)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hProgressions, eventually_ge_atTop (Real.exp 1)] with y hProg hy
  have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos 1) hy
  have hlog : 1 ≤ Real.log y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hy
  have hr : (1 : ℝ) ≤ Real.log y ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact hlog
  have hr' : (↑(1 : ℕ) : ℝ) ≤ Real.log y ^ (1 : ℝ) := by exact_mod_cast hr
  have hprog := hProg 1 0 (by norm_num) hr' (by simp : Nat.Coprime 0 1)
  have hfilter : (primesUpTo y).filter (fun p : ℕ => p % 1 = 0) = primesUpTo y := by
    ext p
    simp [Nat.mod_one]
  simpa [li, hfilter, Nat.totient_one] using hprog

/-- The ordinary prime Euler product is positive at every finite cutoff. -/
theorem sieveProduct_pos (y : ℝ) : 0 < sieveProduct y := by
  classical
  unfold sieveProduct
  apply Finset.prod_pos
  intro p hp
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
  have hp0 : 0 < (p : ℝ) := by positivity
  have hrecip : 1 / (p : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    nlinarith
  have hfactor : (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by linarith
  simpa only [one_div] using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hfactor

/-- The odd shifted sieve product is positive at every finite cutoff. -/
theorem shiftedSieveProduct_pos (y : ℝ) :
    0 < shiftedSieveProduct y := by
  classical
  unfold shiftedSieveProduct
  apply Finset.prod_pos
  intro p hp
  have hpErase := Finset.mem_erase.mp hp
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpErase.2).2
  have hpne2 : p ≠ 2 := hpErase.1
  have hp3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hpPrime.two_le
    omega
  have hpCast : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hden : 0 < (p : ℝ) - 1 := by linarith
  have hrecip : 1 / ((p : ℝ) - 1) ≤ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have hfactor : (1 / 2 : ℝ) ≤ 1 - 1 / ((p : ℝ) - 1) := by linarith
  simpa only [one_div] using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hfactor

/-- The product limit controls the reciprocal-prime mass on any fixed power
interval from above. -/
theorem eventually_prime_reciprocal_power_interval_le
    (hc : ClassicalInputs) (a b ε : ℝ)
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ (primesUpTo (x ^ b)).filter (fun p : ℕ => x ^ a < (p : ℝ)),
        1 / (p : ℝ)) ≤ Real.log (b / a) + ε := by
  let E : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have hE : 0 < E := Real.exp_pos _
  have hA : Tendsto
      (fun x : ℝ => Real.log (x ^ a) * sieveProduct (x ^ a)) atTop (nhds E) :=
    hc.mertens.2.comp (tendsto_rpow_atTop ha)
  have hB : Tendsto
      (fun x : ℝ => Real.log (x ^ b) * sieveProduct (x ^ b)) atTop (nhds E) :=
    hc.mertens.2.comp (tendsto_rpow_atTop (lt_trans ha hab))
  have hAux : Tendsto
      (fun x : ℝ =>
        (Real.log (x ^ b) * sieveProduct (x ^ b)) /
          (Real.log (x ^ a) * sieveProduct (x ^ a))) atTop (nhds 1) := by
    have hdiv := hB.div hA (ne_of_gt hE)
    have hEE : E / E = 1 := div_self hE.ne'
    have hfun :
        (fun x : ℝ =>
          (Real.log (x ^ b) * sieveProduct (x ^ b)) /
            (Real.log (x ^ a) * sieveProduct (x ^ a))) =
          (fun x : ℝ => Real.log (x ^ b) * sieveProduct (x ^ b)) /
            (fun x : ℝ => Real.log (x ^ a) * sieveProduct (x ^ a)) := by
      funext x
      rfl
    rw [hfun]
    simpa only [hEE] using hdiv
  have hAuxScaled : Tendsto
      (fun x : ℝ =>
        ((Real.log (x ^ b) * sieveProduct (x ^ b)) /
          (Real.log (x ^ a) * sieveProduct (x ^ a))) * (a / b))
      atTop (nhds (a / b)) := by
    convert hAux.mul_const (a / b) using 1 <;> simp
  have hRatio : Tendsto
      (fun x : ℝ => sieveProduct (x ^ b) / sieveProduct (x ^ a))
      atTop (nhds (a / b)) := by
    apply (tendsto_congr' ?_).2 hAuxScaled
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx
    have hlogx : 0 < Real.log x := Real.log_pos hx
    have hlogA : Real.log (x ^ a) = a * Real.log x := Real.log_rpow hxpos a
    have hlogB : Real.log (x ^ b) = b * Real.log x := Real.log_rpow hxpos b
    have hVA : 0 < sieveProduct (x ^ a) := sieveProduct_pos _
    have hVB : 0 < sieveProduct (x ^ b) := sieveProduct_pos _
    rw [hlogA, hlogB]
    field_simp [ne_of_gt ha, ne_of_gt (lt_trans ha hab), ne_of_gt hlogx,
      ne_of_gt hVA, ne_of_gt hVB]
    <;> ring
  have habPos : 0 < b / a := div_pos (lt_trans ha hab) ha
  have hlogRatio := (Real.continuousAt_log (ne_of_gt (div_pos ha (lt_trans ha hab)))).tendsto.comp hRatio
  have hneglog : -Real.log (a / b) = Real.log (b / a) := by
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt (lt_trans ha hab)),
      Real.log_div (ne_of_gt (lt_trans ha hab)) (ne_of_gt ha)]
    ring
  have hNegLog : Tendsto
      (fun x : ℝ => -Real.log (sieveProduct (x ^ b) / sieveProduct (x ^ a)))
      atTop (nhds (Real.log (b / a))) := by
    simpa [hneglog] using hlogRatio.neg
  have hClose : ∀ᶠ x : ℝ in atTop,
      -Real.log (sieveProduct (x ^ b) / sieveProduct (x ^ a)) <
        Real.log (b / a) + ε :=
    hNegLog.eventually (Iio_mem_nhds (by linarith [hε]))
  filter_upwards [hClose, eventually_gt_atTop (1 : ℝ)] with x hClose hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hylo : 0 < x ^ a := Real.rpow_pos_of_pos hxpos _
  have hyhi : 0 < x ^ b := Real.rpow_pos_of_pos hxpos _
  have hyle : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hab.le
  have hFilter := primesUpTo_filter_le_eq (x ^ a) (x ^ b) hylo.le hyle
  let s := primesUpTo (x ^ b)
  let t := primesUpTo (x ^ a)
  have hsub : t ⊆ s := by
    change primesUpTo (x ^ a) ⊆ primesUpTo (x ^ b)
    rw [← hFilter]
    exact Finset.filter_subset _ _
  have hdiff : s \ t = s.filter (fun p : ℕ => x ^ a < (p : ℝ)) := by
    change primesUpTo (x ^ b) \ primesUpTo (x ^ a) =
      (primesUpTo (x ^ b)).filter (fun p : ℕ => x ^ a < (p : ℝ))
    rw [← hFilter]
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hpS, hnot⟩
      refine ⟨hpS, ?_⟩
      by_contra hnotGt
      exact hnot ⟨hpS, le_of_not_gt hnotGt⟩
    · rintro ⟨hpS, hgt⟩
      refine ⟨hpS, ?_⟩
      intro hmem
      exact (not_le_of_gt hgt) hmem.2
  let P := s.filter (fun q : ℕ => x ^ a < (q : ℝ))
  have hprodDiff :
      (∏ p ∈ P, (1 - 1 / (p : ℝ))) =
        sieveProduct (x ^ b) / sieveProduct (x ^ a) := by
    dsimp [P]
    rw [← hdiff]
    have hprodSdiff :
        (∏ p ∈ s \ t, (1 - 1 / (p : ℝ))) *
            (∏ p ∈ t, (1 - 1 / (p : ℝ))) =
          ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
      Finset.prod_sdiff (f := fun p : ℕ => 1 - 1 / (p : ℝ)) hsub
    have htpos : 0 < ∏ p ∈ t, (1 - 1 / (p : ℝ)) := by
      simpa [t, sieveProduct] using sieveProduct_pos (x ^ a)
    calc
      _ = ((∏ p ∈ s \ t, (1 - 1 / (p : ℝ))) *
            (∏ p ∈ t, (1 - 1 / (p : ℝ)))) /
              (∏ p ∈ t, (1 - 1 / (p : ℝ))) := by
        field_simp [ne_of_gt htpos]
      _ = (∏ p ∈ s, (1 - 1 / (p : ℝ))) /
            (∏ p ∈ t, (1 - 1 / (p : ℝ))) := by rw [hprodSdiff]
      _ = _ := by simp [s, t, sieveProduct]
  have hfactorPos (p : ℕ) (hp : p ∈ P) :
      0 < 1 - 1 / (p : ℝ) := by
    have hpS := (Finset.mem_filter.mp hp).1
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpS).2
    have hpCast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
    have hp0 : 0 < (p : ℝ) := by positivity
    have hrecip : 1 / (p : ℝ) ≤ (1 / 2 : ℝ) := by
      rw [div_le_div_iff₀ hp0 (by norm_num)]
      nlinarith
    have hfactor : (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by linarith
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hfactor
  have hlogProd :
      Real.log (sieveProduct (x ^ b) / sieveProduct (x ^ a)) =
        ∑ p ∈ P, Real.log (1 - 1 / (p : ℝ)) := by
    rw [← hprodDiff, Real.log_prod]
    intro p hp
    exact ne_of_gt (hfactorPos p hp)
  have hprimeTerm (p : ℕ)
      (hp : p ∈ P) :
      1 / (p : ℝ) ≤ -Real.log (1 - 1 / (p : ℝ)) := by
    have hpS := (Finset.mem_filter.mp hp).1
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpS).2
    have hpCast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
    have hp0 : 0 < (p : ℝ) := by positivity
    have hrecip : 1 / (p : ℝ) ≤ (1 / 2 : ℝ) := by
      rw [div_le_div_iff₀ hp0 (by norm_num)]
      nlinarith
    have hbase : 0 < 1 - 1 / (p : ℝ) := by linarith
    have hlog := Real.add_one_le_exp (Real.log (1 - 1 / (p : ℝ)))
    rw [Real.exp_log hbase] at hlog
    linarith
  have hsumLe :
      (∑ p ∈ P, 1 / (p : ℝ)) ≤
        -Real.log (sieveProduct (x ^ b) / sieveProduct (x ^ a)) := by
    calc
      _ ≤ ∑ p ∈ P, -Real.log (1 - 1 / (p : ℝ)) :=
          Finset.sum_le_sum (fun p hp => hprimeTerm p hp)
      _ = -Real.log (sieveProduct (x ^ b) / sieveProduct (x ^ a)) := by
        rw [Finset.sum_neg_distrib, hlogProd]
  exact le_trans hsumLe hClose.le

/-- The shifted sieve density `1/(p-1)` has the same power-interval upper
mass as `1/p`, since the two weights are asymptotic uniformly on the interval. -/
theorem eventually_shifted_prime_reciprocal_power_interval_le
    (hc : ClassicalInputs) (a b ε : ℝ)
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ (primesUpTo (x ^ b)).filter (fun p : ℕ => x ^ a < (p : ℝ)),
        1 / ((p : ℝ) - 1)) ≤ Real.log (b / a) + ε := by
  have hratio : 1 < b / a := by
    rw [lt_div_iff₀ ha]
    simpa using hab
  have hcpos : 0 < Real.log (b / a) := Real.log_pos hratio
  let η : ℝ := min (ε / 4) 1
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηeps : η ≤ ε / 4 := min_le_left _ _
  have hηone : η ≤ 1 := min_le_right _ _
  have hRecip := eventually_prime_reciprocal_power_interval_le hc a b η ha hab hη
  have hPow2 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ a :=
    (tendsto_rpow_atTop ha).eventually (eventually_ge_atTop 2)
  have hTail : ∀ᶠ x : ℝ in atTop,
      2 * (Real.log (b / a) + 1) / (x ^ a) < ε / 2 := by
    have htendsto : Tendsto
        (fun x : ℝ => 2 * (Real.log (b / a) + 1) / (x ^ a)) atTop (nhds 0) :=
      (tendsto_rpow_atTop ha).const_div_atTop (2 * (Real.log (b / a) + 1))
    exact htendsto.eventually (Iio_mem_nhds (by positivity))
  have hX : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  filter_upwards [hRecip, hPow2, hTail, hX] with x hRecip hxpow hTail hx
  let P := (primesUpTo (x ^ b)).filter (fun p : ℕ => x ^ a < (p : ℝ))
  have hFactor : ∀ p ∈ P,
      1 / ((p : ℝ) - 1) ≤ (1 + 2 / (x ^ a)) * (1 / (p : ℝ)) := by
    intro p hp
    have hpgt : x ^ a < (p : ℝ) := (Finset.mem_filter.mp hp).2
    have hpS := (Finset.mem_filter.mp hp).1
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpS).2
    have hpCast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
    have hp0 : 0 < (p : ℝ) := by positivity
    have hden : 0 < (p : ℝ) - 1 := by linarith
    have hxapos : 0 < x ^ a := Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) _
    have hdenLower : x ^ a / 2 ≤ (p : ℝ) - 1 := by nlinarith [hpgt, hxpow]
    have hmul : 1 ≤ (2 / (x ^ a)) * ((p : ℝ) - 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hxapos]
      nlinarith [hdenLower]
    have hnum : 1 / ((p : ℝ) - 1) ≤ (1 + 2 / (x ^ a)) / (p : ℝ) := by
      apply (div_le_div_iff₀ hden hp0).2
      have hprod : (p : ℝ) = ((p : ℝ) - 1) + 1 := by ring
      rw [hprod]
      have hmul' : 1 ≤ (2 / (x ^ a)) * ((p : ℝ) - 1) := hmul
      nlinarith [hmul']
    calc
      1 / ((p : ℝ) - 1) ≤ (1 + 2 / (x ^ a)) / (p : ℝ) := hnum
      _ = (1 + 2 / (x ^ a)) * (1 / (p : ℝ)) := by ring
  have hSumUpper :
      (∑ p ∈ P, 1 / ((p : ℝ) - 1)) ≤
        (1 + 2 / (x ^ a)) * (∑ p ∈ P, 1 / (p : ℝ)) := by
    calc
      _ ≤ ∑ p ∈ P, (1 + 2 / (x ^ a)) * (1 / (p : ℝ)) :=
        Finset.sum_le_sum (fun p hp => hFactor p hp)
      _ = (1 + 2 / (x ^ a)) * (∑ p ∈ P, 1 / (p : ℝ)) := by
        rw [← Finset.mul_sum]
  have hSumNonneg : 0 ≤ ∑ p ∈ P, 1 / (p : ℝ) :=
    Finset.sum_nonneg fun p hp => by positivity
  have hSumBound : ∑ p ∈ P, 1 / (p : ℝ) ≤ Real.log (b / a) + η := hRecip
  have hBaseBound : Real.log (b / a) + η ≤ Real.log (b / a) + 1 :=
    add_le_add_right hηone (Real.log (b / a))
  have hErrFactor : (2 / (x ^ a)) * (∑ p ∈ P, 1 / (p : ℝ)) ≤ ε / 2 := by
    have hfactor1 := mul_le_mul_of_nonneg_left hSumBound
      (by positivity : 0 ≤ 2 / (x ^ a))
    have hfactor2 := mul_le_mul_of_nonneg_left hBaseBound
      (by positivity : 0 ≤ 2 / (x ^ a))
    have hstrict : (2 / (x ^ a)) * (∑ p ∈ P, 1 / (p : ℝ)) < ε / 2 := by
      calc
        (2 / (x ^ a)) * (∑ p ∈ P, 1 / (p : ℝ)) ≤
            (2 / (x ^ a)) * (Real.log (b / a) + η) := hfactor1
        _ ≤ (2 / (x ^ a)) * (Real.log (b / a) + 1) := hfactor2
        _ < ε / 2 := by
          calc
            (2 / (x ^ a)) * (Real.log (b / a) + 1) =
                2 * (Real.log (b / a) + 1) / (x ^ a) := by ring
            _ < ε / 2 := hTail
    exact hstrict.le
  calc
    (∑ p ∈ P, 1 / ((p : ℝ) - 1)) ≤
        (1 + 2 / (x ^ a)) * (∑ p ∈ P, 1 / (p : ℝ)) := hSumUpper
    _ = (∑ p ∈ P, 1 / (p : ℝ)) +
          (2 / (x ^ a)) * (∑ p ∈ P, 1 / (p : ℝ)) := by ring
    _ ≤ Real.log (b / a) + η + ε / 2 := by linarith [hSumBound, hErrFactor]
    _ ≤ Real.log (b / a) + ε := by linarith [hηeps]

/-- Mertens' bounded error gives a uniform reciprocal-prime mass on every
interval `(w,w²]`. -/
theorem prime_reciprocal_interval_bound (hc : ClassicalInputs) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 2 ≤ w →
      (∑ p ∈ ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))),
        1 / (p : ℝ)) ≤ C := by
  obtain ⟨K, hMertens⟩ := hc.mertens.1
  let K₀ : ℝ := |K| + 1
  let C₀ : ℝ := Real.log 2 + 2 * K₀
  have hK : K ≤ K₀ := by dsimp [K₀]; linarith [le_abs_self K]
  refine ⟨C₀, ?_, ?_⟩
  · dsimp [C₀, K₀]
    positivity
  · intro w hw
    have hw0 : 0 ≤ w := le_trans (by norm_num) hw
    have hwle : w ≤ w ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr (by norm_num : (1 : ℝ) ≤ 2))]
    have hset := primesUpTo_filter_le_eq w (w ^ 2) hw0 hwle
    let s := primesUpTo (w ^ 2)
    have hsplit :
        (∑ p ∈ (s.filter (fun p : ℕ => (p : ℝ) ≤ w)), 1 / (p : ℝ)) +
          (∑ p ∈ (s.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ w))), 1 / (p : ℝ)) =
            ∑ p ∈ s, 1 / (p : ℝ) :=
      Finset.sum_filter_add_sum_filter_not s (fun p : ℕ => (p : ℝ) ≤ w)
        (fun p => 1 / (p : ℝ))
    have hnot : s.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ w)) =
        s.filter (fun p : ℕ => w < (p : ℝ)) := by
      ext p
      simp
    have hsum :
        (∑ p ∈ (s.filter (fun p : ℕ => w < (p : ℝ))), 1 / (p : ℝ)) =
          (∑ p ∈ s, 1 / (p : ℝ)) -
            (∑ p ∈ primesUpTo w, 1 / (p : ℝ)) := by
      rw [← hset, ← hnot]
      linarith [hsplit]
    simp only [one_div] at hsum
    have hw2 : 2 ≤ w ^ 2 := by nlinarith
    have hMlo := hMertens w hw
    have hMhi := hMertens (w ^ 2) hw2
    have hlogw : Real.log (w ^ 2) = 2 * Real.log w := by
      rw [Real.log_pow]
      norm_num
    have hlogpos : 0 < Real.log w := Real.log_pos (by linarith)
    have hlogdiff :
        Real.log (Real.log (w ^ 2)) - Real.log (Real.log w) = Real.log 2 := by
      rw [hlogw, Real.log_mul (by norm_num) hlogpos.ne']
      ring
    have hinterval :
        (∑ p ∈ (s.filter (fun p : ℕ => w < (p : ℝ))), 1 / (p : ℝ)) ≤ C₀ := by
      simp only [one_div]
      rw [hsum]
      have hlo := (abs_le.mp hMlo).1
      have hhi := (abs_le.mp hMhi).2
      dsimp [C₀, K₀]
      nlinarith [hlogdiff, hK]
    exact hinterval

/-- The sieve densities `1/(p-1)` also have uniformly bounded mass on
`(w,w²]`. -/
theorem shifted_prime_density_interval_bound (hc : ClassicalInputs) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 2 ≤ w →
      (∑ p ∈ ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))),
        1 / ((p : ℝ) - 1)) ≤ C := by
  obtain ⟨C, hC, hrecip⟩ := prime_reciprocal_interval_bound hc
  refine ⟨(3 / 2 : ℝ) * C, mul_pos (by norm_num) hC, ?_⟩
  intro w hw
  calc
    (∑ p ∈ ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))),
        1 / ((p : ℝ) - 1)) ≤
      ∑ p ∈ ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))),
        (3 / 2 : ℝ) * (1 / (p : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpprime : Nat.Prime p :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          have hwp : w < (p : ℝ) := (Finset.mem_filter.mp hp).2
          have htwo : (2 : ℝ) < (p : ℝ) := lt_of_le_of_lt hw hwp
          have hp3nat : 3 ≤ p := by
            have hp2 : 2 < p := by exact_mod_cast htwo
            omega
          have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3nat
          have hp0 : 0 < (p : ℝ) := by positivity
          have hp1 : 0 < (p : ℝ) - 1 := by linarith
          have hratio : 1 / ((p : ℝ) - 1) ≤ (3 / 2 : ℝ) / (p : ℝ) := by
            rw [div_le_div_iff₀ hp1 hp0]
            nlinarith
          simpa [div_eq_mul_inv] using hratio
    _ = (3 / 2 : ℝ) *
        (∑ p ∈ ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))),
          1 / (p : ℝ)) := by rw [← Finset.mul_sum]
    _ ≤ (3 / 2 : ℝ) * C := mul_le_mul_of_nonneg_left (hrecip w hw) (by norm_num)

/-- Include the short initial range `1 < w < 2` in the same uniform bound. -/
theorem shifted_prime_density_interval_bound_all (hc : ClassicalInputs) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 1 < w →
      (∑ p ∈ ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))),
        1 / ((p : ℝ) - 1)) ≤ C := by
  obtain ⟨C, hC, hlarge⟩ := shifted_prime_density_interval_bound hc
  let C₀ : ℝ := max C 2
  refine ⟨C₀, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro w hw
  by_cases hw2 : 2 ≤ w
  · exact le_trans (hlarge w hw2) (le_max_left _ _)
  · have hwlt : w < 2 := lt_of_not_ge hw2
    have hprod : 0 < (2 - w) * (2 + w) :=
      mul_pos (by linarith) (by linarith)
    have hwSq : w ^ 2 < 4 := by nlinarith [hprod]
    let s := (primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))
    have hsub : s ⊆ ({2, 3} : Finset ℕ) := by
      intro p hp
      have hpUp := (Finset.mem_filter.mp hp).1
      have hpBase := Finset.mem_filter.mp hpUp
      have hpFloor : p ≤ ⌊w ^ 2⌋₊ := (Finset.mem_Icc.mp hpBase.1).2
      have hpReal : (p : ℝ) ≤ w ^ 2 :=
        le_trans (Nat.cast_le.mpr hpFloor) (Nat.floor_le (by positivity))
      have hpLt : p < 4 := by exact_mod_cast lt_of_le_of_lt hpReal hwSq
      have hpPrime : Nat.Prime p := hpBase.2
      have hpTwo : 2 ≤ p := hpPrime.two_le
      have hpEq : p = 2 ∨ p = 3 := by omega
      simpa using hpEq
    have hsum :
        (∑ p ∈ s, 1 / ((p : ℝ) - 1)) ≤
          ∑ p ∈ ({2, 3} : Finset ℕ), 1 / ((p : ℝ) - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      have hpCases : p = 2 ∨ p = 3 := by simpa using hp
      rcases hpCases with rfl | rfl <;> norm_num
    have hvalue :
        (∑ p ∈ ({2, 3} : Finset ℕ), 1 / ((p : ℝ) - 1)) = 3 / 2 := by norm_num
    calc
      (∑ p ∈ s, 1 / ((p : ℝ) - 1)) ≤ 3 / 2 := by rw [← hvalue]; exact hsum
      _ ≤ 2 := by norm_num
      _ ≤ C₀ := le_max_right _ _

/-- The candidate sieve data meet the uniform density conditions required by
the block sieve, given a uniform prime-interval bound. -/
theorem candidateSieve_densityBounds_fromInterval (C : CandidateData)
    (x : ℝ) (jstar : ℕ) (y : ℝ)
    (K : ℝ)
    (hInterval : ∀ w : ℝ, 1 < w →
      (∑ p ∈ ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))),
        1 / ((p : ℝ) - 1)) ≤ K)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (hy : 1 < y) :
    (candidateSieveData C x jstar y hweight hmass).densityBounds y (1 / 2) K := by
  refine ⟨hy, by norm_num, ?_, ?_⟩
  · intro p hp
    have hpne : p ≠ 2 := (Finset.mem_erase.mp hp).1
    have hpup := (Finset.mem_erase.mp hp).2
    have hpbase := Finset.mem_filter.mp hpup
    have hpbound := (Finset.mem_Icc.mp hpbase.1).2
    have hpprime : Nat.Prime p := hpbase.2
    have hpcast : (p : ℝ) ≤ y := le_trans (Nat.cast_le.mpr hpbound) (Nat.floor_le (le_of_lt (lt_trans (by norm_num) hy)))
    have hp3 : 3 ≤ p := by
      by_contra h
      have hple : p ≤ 2 := Nat.le_of_not_gt h
      have hp2 : p = 2 := le_antisymm hple hpprime.two_le
      exact hpne hp2
    have hden : 0 < (p : ℝ) - 1 := by linarith [show (3 : ℝ) ≤ p by exact_mod_cast hp3]
    refine ⟨hpcast, ?_, ?_⟩
    · change 0 ≤ 1 / ((p : ℝ) - 1)
      positivity
    · change 1 / ((p : ℝ) - 1) ≤ 1 - (1 / 2 : ℝ)
      rw [show 1 - (1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num]
      rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
      nlinarith [show (3 : ℝ) ≤ p by exact_mod_cast hp3]
  · intro w hw
    let s : Finset ℕ := (candidateSieveData C x jstar y hweight hmass).primes.filter
      (fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ 2)
    let t : Finset ℕ := (primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ))
    have hsub : s ⊆ t := by
      intro p hp
      have hpcond := Finset.mem_filter.mp hp
      have hpprime : Nat.Prime p :=
        (candidateSieveData C x jstar y hweight hmass).prime p hpcond.1
      have hpcast : (p : ℝ) ≤ w ^ 2 := hpcond.2.2
      have hfloor : p ≤ ⌊w ^ 2⌋₊ := (Nat.le_floor_iff (by positivity)).2 hpcast
      have hpIcc : p ∈ Finset.Icc 1 ⌊w ^ 2⌋₊ :=
        Finset.mem_Icc.mpr ⟨le_trans (by norm_num) hpprime.two_le, hfloor⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hpIcc, hpprime⟩, hpcond.2.1⟩
    have hsum :
        (∑ p ∈ s, (candidateSieveData C x jstar y hweight hmass).density p) ≤
          ∑ p ∈ t, 1 / ((p : ℝ) - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      have hpup := (Finset.mem_filter.mp hp).1
      have hpprime : Nat.Prime p := (Finset.mem_filter.mp hpup).2
      have hp2 : 2 ≤ p := hpprime.two_le
      have hp2real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have hpden : 0 < (p : ℝ) - 1 := by linarith
      change 0 ≤ 1 / ((p : ℝ) - 1)
      positivity
    have hbound := hInterval w hw
    dsimp [s, t, candidateSieveData] at hsum ⊢
    exact le_trans hsum hbound

/-- Mertens' theorem supplies the uniform interval bound for the candidate
sieve density conditions. -/
theorem candidateSieve_densityBounds (hc : ClassicalInputs) (C : CandidateData)
    (x : ℝ) (jstar : ℕ) (y : ℝ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (hy : 1 < y) :
    ∃ K : ℝ, 0 < K ∧
      (candidateSieveData C x jstar y hweight hmass).densityBounds y (1 / 2) K := by
  obtain ⟨K, hK, hInterval⟩ := shifted_prime_density_interval_bound_all hc
  exact ⟨K, hK, candidateSieve_densityBounds_fromInterval C x jstar y K hInterval
    hweight hmass hy⟩

/-- Mertens density bounds also apply after restricting the sieve weight to a
fixed prime divisor. -/
theorem primeDivisorSieve_densityBounds (C : CandidateData) (x : ℝ)
    (jstar p : ℕ) (y K : ℝ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (hInterval : ∀ w : ℝ, 1 < w →
      (∑ q ∈ ((primesUpTo (w ^ 2)).filter (fun q : ℕ => w < (q : ℝ))),
        1 / ((q : ℝ) - 1)) ≤ K) (hy : 1 < y) :
    (primeDivisorSieveData C x jstar p y hweight hmass).densityBounds y (1 / 2) K := by
  simpa [SieveData.densityBounds, primeDivisorSieveData, candidateSieveData] using
    candidateSieve_densityBounds_fromInterval C x jstar y K hInterval hweight hmass hy

/-- Upper-sieve the candidate mass on multiples of a set of large primes.
The remainder terms inject into the Type I modulus range. -/
theorem primeDivisorSiftedMass_sum_upper
    (B : BlockSieve) (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (y θ Kdens : ℝ) (P : Finset ℕ)
    (hX : 0 ≤ x) (hY : 2 ≤ y) (hKdens : 0 < Kdens)
    (hInterval : ∀ w : ℝ, 1 < w →
      (∑ q ∈ ((primesUpTo (w ^ 2)).filter (fun q : ℕ => w < (q : ℝ))),
        1 / ((q : ℝ) - 1)) ≤ Kdens)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar)
    (hpPrime : ∀ p ∈ P, Nat.Prime p)
    (hpLarge : ∀ p ∈ P, y < (p : ℝ))
    (hLevel : ∀ p ∈ P, ∀ d ∈ smallSieveModuli y (y ^ 10),
      (p * d : ℝ) ≤ x ^ θ) :
    ∃ Kblock : ℝ, 0 < Kblock ∧
      (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) ≤
        Kblock * C.mass x jstar * shiftedSieveProduct y *
            (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
          Kblock *
            (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun e => Odd e ∧ Squarefree e)),
              |C.remainder x jstar e|) := by
  obtain ⟨Kblock, hKblock, h₀, hBlock⟩ := B (1 / 2) Kdens (by norm_num) hKdens
  let Dsmall := smallSieveModuli y (y ^ 10)
  have hRemPairs :
      (∑ p ∈ P, ∑ d ∈ Dsmall, |C.remainder x jstar (p * d)|) ≤
        ∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun e => Odd e ∧ Squarefree e)),
          |C.remainder x jstar e| := by
    apply prime_sieve_remainders_le_typeI C x jstar θ y P Dsmall hX hpPrime hpLarge
    · intro d hd
      have hd' : d ∈ (Finset.Icc 1 ⌊y ^ 10⌋₊).filter
          (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2) := by
        simpa [Dsmall, smallSieveModuli] using hd
      have hdIcc := (Finset.mem_filter.mp hd').1
      exact Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdIcc).1)
    · intro d hd q hq
      have hd' : d ∈ (Finset.Icc 1 ⌊y ^ 10⌋₊).filter
          (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2) := by
        simpa [Dsmall, smallSieveModuli] using hd
      have hqS : q ∈ (primesUpTo y).erase 2 :=
        (Finset.mem_filter.mp hd').2.2 hq
      have hqUp := (Finset.mem_erase.mp hqS).2
      have hqBase := Finset.mem_filter.mp hqUp
      have hqFloor := (Finset.mem_Icc.mp hqBase.1).2
      exact le_trans (Nat.cast_le.mpr hqFloor)
        (Nat.floor_le (le_trans (by norm_num : (0 : ℝ) ≤ 2) hY))
    · intro p hp d hd
      have hd' : d ∈ (Finset.Icc 1 ⌊y ^ 10⌋₊).filter
          (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2) := by
        simpa [Dsmall, smallSieveModuli] using hd
      have hSq : Squarefree d := (Finset.mem_filter.mp hd').2.1
      have hsubset : d.primeFactors ⊆ (primeDivisorSieveData C x jstar p y
          hweight hmass).primes := by
        simpa [primeDivisorSieveData] using (Finset.mem_filter.mp hd').2.2
      have hdOdd : Odd d := by
        by_contra hodd
        have heven : Even d := Nat.not_odd_iff_even.mp hodd
        have h2dvd : 2 ∣ d := even_iff_two_dvd.mp heven
        have hdpos : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hd').1).1
        have h2mem : 2 ∈ d.primeFactors :=
          (Nat.mem_primeFactors_of_ne_zero hdpos.ne').2 ⟨Nat.prime_two, h2dvd⟩
        have h2sieve := hsubset h2mem
        exact (Finset.mem_erase.mp h2sieve).1 rfl
      have hp3 : 3 ≤ p := by
        have hpgt : (2 : ℝ) < (p : ℝ) := lt_of_le_of_lt hY (hpLarge p hp)
        have hpNat : 2 < p := by exact_mod_cast hpgt
        omega
      have hpOdd : Odd p := (hpPrime p hp).odd_iff.mpr hp3
      have hcop := primeDivisorSieve_coprime C x jstar p y (hpPrime p hp)
        hweight hmass (by linarith [hY]) hSq hsubset (hpLarge p hp)
      refine ⟨Nat.odd_mul.mpr ⟨hpOdd, hdOdd⟩, ?_, hLevel p hp d hd⟩
      exact (Nat.squarefree_mul hcop).2 ⟨(hpPrime p hp).squarefree, hSq⟩
  have hsumMain :
      (∑ p ∈ P, Kblock * (C.mass x jstar / ((p : ℝ) - 1)) *
        shiftedSieveProduct y) =
        Kblock * C.mass x jstar * shiftedSieveProduct y *
          (∑ p ∈ P, 1 / ((p : ℝ) - 1)) := by
    calc
      _ = ∑ p ∈ P, (Kblock * C.mass x jstar * shiftedSieveProduct y) *
            (1 / ((p : ℝ) - 1)) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
      _ = _ := by rw [← Finset.mul_sum]
  have hsumRem :
      (∑ p ∈ P, (primeDivisorSieveData C x jstar p y hweight hmass).remainderSum
        (y ^ 10)) =
        ∑ p ∈ P, ∑ d ∈ Dsmall, |C.remainder x jstar (p * d)| := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [SieveData.remainderSum, primeDivisorSieve_products]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d ∈ (Finset.Icc 1 ⌊y ^ 10⌋₊).filter
        (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2) := by
      simpa [Dsmall, smallSieveModuli] using hd
    have hSq : Squarefree d := (Finset.mem_filter.mp hd').2.1
    have hsubset : d.primeFactors ⊆
        (primeDivisorSieveData C x jstar p y hweight hmass).primes := by
      simpa [primeDivisorSieveData] using (Finset.mem_filter.mp hd').2.2
    rw [primeDivisorSieve_remainder C x jstar p y (hpPrime p hp) hweight hmass
      (by linarith [hY]) hSq hsubset (hpLarge p hp)]
  have hsum :
      (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) ≤
        ∑ p ∈ P,
          (Kblock * (C.mass x jstar / ((p : ℝ) - 1)) * shiftedSieveProduct y +
            Kblock * (primeDivisorSieveData C x jstar p y hweight hmass).remainderSum
              (y ^ 10)) := by
    apply Finset.sum_le_sum
    intro p hp
    let S := primeDivisorSieveData C x jstar p y hweight hmass
    have hDens := primeDivisorSieve_densityBounds C x jstar p y Kdens
      hweight hmass hInterval (by linarith [hY])
    have hUpper := (hBlock ℕ S y hDens).1
    have hSift := primeDivisorSieve_sifted_eq C x jstar p y hweight hmass
    have hProduct := primeDivisorSieve_product C x jstar p y hweight hmass
    have hφ : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
      have hp1 : 1 ≤ p := (hpPrime p hp).one_le
      rw [Nat.totient_prime (hpPrime p hp), Nat.cast_sub hp1]
      norm_num
    have hSift' : S.sifted = primeDivisorSiftedMass C x jstar p y := by
      simpa [S] using hSift
    rw [hSift'] at hUpper
    have hProduct' : S.product = shiftedSieveProduct y := by
      simpa [S] using hProduct
    rw [hProduct'] at hUpper
    simpa [S, SieveData.X, primeDivisorSieveData, hφ] using hUpper
  have hsumRemainder := add_le_add_left
    (mul_le_mul_of_nonneg_left hRemPairs hKblock.le)
    (Kblock * C.mass x jstar * shiftedSieveProduct y *
      ∑ p ∈ P, 1 / ((p : ℝ) - 1))
  refine ⟨Kblock, hKblock, ?_⟩
  calc
    (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) ≤
        ∑ p ∈ P,
          (Kblock * (C.mass x jstar / ((p : ℝ) - 1)) * shiftedSieveProduct y +
            Kblock * (primeDivisorSieveData C x jstar p y hweight hmass).remainderSum
              (y ^ 10)) := hsum
    _ = Kblock * C.mass x jstar * shiftedSieveProduct y *
          (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
        Kblock * (∑ p ∈ P, ∑ d ∈ Dsmall, |C.remainder x jstar (p * d)|) := by
          rw [Finset.sum_add_distrib, hsumMain, ← Finset.mul_sum, hsumRem]
    _ ≤ Kblock * C.mass x jstar * shiftedSieveProduct y *
          (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
        Kblock *
          (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun e => Odd e ∧ Squarefree e)),
            |C.remainder x jstar e|) := by nlinarith [hsumRemainder]

/-- The estimate supplied by `BlockSieve` after its density parameters and
uniform constant have been fixed. -/
def BlockSieveWitness (Kdens Kblock : ℝ) (h₀ : ℕ) : Prop :=
  ∀ (α : Type) (S : SieveData α) (z : ℝ),
    S.densityBounds z (1 / 2) Kdens →
      (S.sifted ≤ Kblock * S.X * S.product +
          Kblock * S.remainderSum (z ^ (10 : ℕ))) ∧
        ∀ h : ℕ, h₀ ≤ h → Even h →
          |S.sifted - S.X * S.product| ≤
              Kblock * Real.exp (-(h : ℝ)) * S.X * S.product +
                Kblock * S.remainderSum (z ^ (4 * h + 2)) ∧
            ∃ u v : ℕ → ℝ,
              (∀ d, |u d| ≤ 1 ∧ |v d| ≤ 1 ∧ |u d - v d| ≤ 1) ∧
                (∀ d, d ∉ S.products (z ^ (4 * h + 2)) → u d = 0 ∧ v d = 0) ∧
                  ∀ a ∈ S.objects,
                    let D := z ^ (4 * h + 2)
                    let I : ℝ := if ∀ p ∈ S.primes, ¬ S.bad p a then 1 else 0
                    S.polynomial D v a ≤ I ∧ I ≤ S.polynomial D u a ∧
                      0 ≤ S.polynomial D u a ∧
                        S.polynomial D u a - I ≤
                          S.polynomial D (fun d => u d - v d) a

/-- The fixed-prime sieve has a sharp main term once its depth is large;
the only other contribution is the Type I remainder sum. -/
theorem primeDivisorSiftedMass_sum_refined_upper_core
    (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (y θ Kdens : ℝ) (P : Finset ℕ)
    (Kblock : ℝ) (hKblock : 0 < Kblock) (h₀ : ℕ)
    (hBlock : BlockSieveWitness Kdens Kblock h₀)
    (hX : 0 ≤ x) (hY : 2 ≤ y)
    (hInterval : ∀ w : ℝ, 1 < w →
      (∑ q ∈ ((primesUpTo (w ^ 2)).filter (fun q : ℕ => w < (q : ℝ))),
        1 / ((q : ℝ) - 1)) ≤ Kdens)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar)
    (hpPrime : ∀ p ∈ P, Nat.Prime p)
    (hpLarge : ∀ p ∈ P, y < (p : ℝ)) :
      ∀ h : ℕ, h₀ ≤ h → Even h →
        (∀ p ∈ P, ∀ d ∈ smallSieveModuli y (y ^ (4 * h + 2)),
          (p * d : ℝ) ≤ x ^ θ) →
        (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) ≤
          (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
              shiftedSieveProduct y * (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
            Kblock *
              (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                  (fun e => Odd e ∧ Squarefree e)),
                |C.remainder x jstar e|) := by
  intro h hh heven hLevel
  let Dsmall := smallSieveModuli y (y ^ (4 * h + 2))
  have hRemPairs :
      (∑ p ∈ P, ∑ d ∈ Dsmall, |C.remainder x jstar (p * d)|) ≤
        ∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
            (fun e => Odd e ∧ Squarefree e)),
          |C.remainder x jstar e| := by
    apply prime_sieve_remainders_le_typeI C x jstar θ y P Dsmall hX hpPrime hpLarge
    · intro d hd
      have hd' : d ∈ (Finset.Icc 1 ⌊y ^ (4 * h + 2)⌋₊).filter
          (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2) := by
        simpa [Dsmall, smallSieveModuli] using hd
      have hdIcc := (Finset.mem_filter.mp hd').1
      exact Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp hdIcc).1)
    · intro d hd q hq
      have hd' : d ∈ (Finset.Icc 1 ⌊y ^ (4 * h + 2)⌋₊).filter
          (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2) := by
        simpa [Dsmall, smallSieveModuli] using hd
      have hqS : q ∈ (primesUpTo y).erase 2 :=
        (Finset.mem_filter.mp hd').2.2 hq
      have hqBase := Finset.mem_filter.mp (Finset.mem_erase.mp hqS).2
      have hqFloor := (Finset.mem_Icc.mp hqBase.1).2
      exact le_trans (Nat.cast_le.mpr hqFloor)
        (Nat.floor_le (le_trans (by norm_num : (0 : ℝ) ≤ 2) hY))
    · intro p hp d hd
      have hd' : d ∈ (Finset.Icc 1 ⌊y ^ (4 * h + 2)⌋₊).filter
          (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2) := by
        simpa [Dsmall, smallSieveModuli] using hd
      have hSq : Squarefree d := (Finset.mem_filter.mp hd').2.1
      have hsubset : d.primeFactors ⊆
          (primeDivisorSieveData C x jstar p y hweight hmass).primes := by
        simpa [primeDivisorSieveData] using (Finset.mem_filter.mp hd').2.2
      have hdOdd : Odd d := by
        by_contra hodd
        have hevenD : Even d := Nat.not_odd_iff_even.mp hodd
        have h2dvd : 2 ∣ d := even_iff_two_dvd.mp hevenD
        have hdpos : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hd').1).1
        have h2mem : 2 ∈ d.primeFactors :=
          (Nat.mem_primeFactors_of_ne_zero hdpos.ne').2 ⟨Nat.prime_two, h2dvd⟩
        have h2sieve := hsubset h2mem
        exact (Finset.mem_erase.mp h2sieve).1 rfl
      have hp3 : 3 ≤ p := by
        have hpgt : (2 : ℝ) < (p : ℝ) := lt_of_le_of_lt hY (hpLarge p hp)
        have hpNat : 2 < p := by exact_mod_cast hpgt
        omega
      have hpOdd : Odd p := (hpPrime p hp).odd_iff.mpr hp3
      have hcop := primeDivisorSieve_coprime C x jstar p y (hpPrime p hp)
        hweight hmass (by linarith [hY]) hSq hsubset (hpLarge p hp)
      refine ⟨Nat.odd_mul.mpr ⟨hpOdd, hdOdd⟩, ?_, hLevel p hp d hd⟩
      exact (Nat.squarefree_mul hcop).2 ⟨(hpPrime p hp).squarefree, hSq⟩
  have hsumMain :
      (∑ p ∈ P, (1 + Kblock * Real.exp (-(h : ℝ))) *
          (C.mass x jstar / ((p : ℝ) - 1)) * shiftedSieveProduct y) =
        (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
          shiftedSieveProduct y * (∑ p ∈ P, 1 / ((p : ℝ) - 1)) := by
    calc
      _ = ∑ p ∈ P, ((1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
            shiftedSieveProduct y) * (1 / ((p : ℝ) - 1)) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
      _ = _ := by rw [← Finset.mul_sum]
  have hsumRem :
      (∑ p ∈ P, (primeDivisorSieveData C x jstar p y hweight hmass).remainderSum
        (y ^ (4 * h + 2))) =
        ∑ p ∈ P, ∑ d ∈ Dsmall, |C.remainder x jstar (p * d)| := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [SieveData.remainderSum, primeDivisorSieve_products]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d ∈ (Finset.Icc 1 ⌊y ^ (4 * h + 2)⌋₊).filter
        (fun d => Squarefree d ∧ d.primeFactors ⊆ (primesUpTo y).erase 2) := by
      simpa [Dsmall, smallSieveModuli] using hd
    have hSq : Squarefree d := (Finset.mem_filter.mp hd').2.1
    have hsubset : d.primeFactors ⊆
        (primeDivisorSieveData C x jstar p y hweight hmass).primes := by
      simpa [primeDivisorSieveData] using (Finset.mem_filter.mp hd').2.2
    rw [primeDivisorSieve_remainder C x jstar p y (hpPrime p hp) hweight hmass
      (by linarith [hY]) hSq hsubset (hpLarge p hp)]
  have hsum :
      (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) ≤
        ∑ p ∈ P,
          ((1 + Kblock * Real.exp (-(h : ℝ))) *
              (C.mass x jstar / ((p : ℝ) - 1)) * shiftedSieveProduct y +
            Kblock * (primeDivisorSieveData C x jstar p y hweight hmass).remainderSum
              (y ^ (4 * h + 2))) := by
    apply Finset.sum_le_sum
    intro p hp
    let S := primeDivisorSieveData C x jstar p y hweight hmass
    have hDens := primeDivisorSieve_densityBounds C x jstar p y Kdens
      hweight hmass hInterval (by linarith [hY])
    have hApprox := (hBlock ℕ S y hDens).2 h hh heven |>.1
    have hprodNonneg : 0 ≤ S.product := by
      dsimp [S, SieveData.product]
      apply Finset.prod_nonneg
      intro q hq
      have hden := (hDens.2.2.1 q hq).2.2
      linarith
    have hmainNonneg : 0 ≤ S.X * S.product := mul_nonneg S.X_nonneg hprodNonneg
    have hdev := (abs_le.mp hApprox).2
    have hUpper : S.sifted ≤
        (1 + Kblock * Real.exp (-(h : ℝ))) * S.X * S.product +
          Kblock * S.remainderSum (y ^ (4 * h + 2)) := by
      calc
        S.sifted ≤ S.X * S.product +
            (Kblock * Real.exp (-(h : ℝ)) * S.X * S.product +
              Kblock * S.remainderSum (y ^ (4 * h + 2))) := by linarith
        _ = _ := by ring
    have hSift := primeDivisorSieve_sifted_eq C x jstar p y hweight hmass
    have hProduct := primeDivisorSieve_product C x jstar p y hweight hmass
    have hProduct' : S.product = shiftedSieveProduct y := by
      simpa [S] using hProduct
    have hp1 : 1 ≤ p := (hpPrime p hp).one_le
    have hφ : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.totient_prime (hpPrime p hp), Nat.cast_sub hp1]
      norm_num
    have hSift' : S.sifted = primeDivisorSiftedMass C x jstar p y := by
      simpa [S] using hSift
    rw [hSift'] at hUpper
    rw [hProduct'] at hUpper
    simpa [S, SieveData.X, primeDivisorSieveData, hφ] using hUpper
  have hsumRemainder := add_le_add_left
    (mul_le_mul_of_nonneg_left hRemPairs hKblock.le)
    ((1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
      shiftedSieveProduct y * (∑ p ∈ P, 1 / ((p : ℝ) - 1)))
  calc
    (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) ≤
        ∑ p ∈ P,
          ((1 + Kblock * Real.exp (-(h : ℝ))) *
              (C.mass x jstar / ((p : ℝ) - 1)) * shiftedSieveProduct y +
            Kblock * (primeDivisorSieveData C x jstar p y hweight hmass).remainderSum
              (y ^ (4 * h + 2))) := hsum
    _ = (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
          shiftedSieveProduct y * (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
        Kblock * (∑ p ∈ P, ∑ d ∈ Dsmall, |C.remainder x jstar (p * d)|) := by
          rw [Finset.sum_add_distrib, hsumMain, ← Finset.mul_sum, hsumRem]
    _ ≤ (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
          shiftedSieveProduct y * (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
        Kblock *
          (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
              (fun e => Odd e ∧ Squarefree e)),
            |C.remainder x jstar e|) := by nlinarith [hsumRemainder]

/-- Instantiate the uniform block-sieve witness for one fixed candidate
parameter. -/
theorem primeDivisorSiftedMass_sum_refined_upper
    (B : BlockSieve) (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (y θ Kdens : ℝ) (P : Finset ℕ)
    (hX : 0 ≤ x) (hY : 2 ≤ y) (hKdens : 0 < Kdens)
    (hInterval : ∀ w : ℝ, 1 < w →
      (∑ q ∈ ((primesUpTo (w ^ 2)).filter (fun q : ℕ => w < (q : ℝ))),
        1 / ((q : ℝ) - 1)) ≤ Kdens)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar)
    (hpPrime : ∀ p ∈ P, Nat.Prime p)
    (hpLarge : ∀ p ∈ P, y < (p : ℝ)) :
    ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
      ∀ h : ℕ, h₀ ≤ h → Even h →
        (∀ p ∈ P, ∀ d ∈ smallSieveModuli y (y ^ (4 * h + 2)),
          (p * d : ℝ) ≤ x ^ θ) →
        (∑ p ∈ P, primeDivisorSiftedMass C x jstar p y) ≤
          (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
              shiftedSieveProduct y * (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
            Kblock *
              (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                  (fun e => Odd e ∧ Squarefree e)),
                |C.remainder x jstar e|) := by
  obtain ⟨Kblock, hKblock, h₀, hBlock⟩ :=
    B (1 / 2) Kdens (by norm_num) hKdens
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  intro h hh heven hLevel
  exact primeDivisorSiftedMass_sum_refined_upper_core C x jstar y θ Kdens P
    Kblock hKblock h₀ hBlock hX hY hInterval hweight hmass hpPrime hpLarge
    h hh heven hLevel

/-- The same refined sieve constants work when the prime set and candidate
parameter vary with `x`. -/
theorem primeDivisorSiftedMass_sum_refined_upper_family
    (B : BlockSieve) (C : CandidateData) (jstar : ℕ)
    (Y : ℝ → ℝ) (P : ℝ → Finset ℕ) (θ Kdens : ℝ)
    (hKdens : 0 < Kdens)
    (hInterval : ∀ w : ℝ, 1 < w →
      (∑ q ∈ ((primesUpTo (w ^ 2)).filter (fun q : ℕ => w < (q : ℝ))),
        1 / ((q : ℝ) - 1)) ≤ Kdens)
    (hpPrime : ∀ x p, p ∈ P x → Nat.Prime p) :
    ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
      ∀ h : ℕ, h₀ ≤ h → Even h →
        ∀ x : ℝ, 0 ≤ x → 2 ≤ Y x →
          (∀ p ∈ P x, Y x < (p : ℝ)) →
          (∀ u, 0 ≤ C.weighted x jstar u) → 0 ≤ C.mass x jstar →
          (∀ p ∈ P x, ∀ d ∈ smallSieveModuli (Y x)
              ((Y x) ^ (4 * h + 2)),
            (p * d : ℝ) ≤ x ^ θ) →
          (∑ p ∈ P x, primeDivisorSiftedMass C x jstar p (Y x)) ≤
            (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
                shiftedSieveProduct (Y x) *
                  (∑ p ∈ P x, 1 / ((p : ℝ) - 1)) +
              Kblock *
                (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                    (fun e => Odd e ∧ Squarefree e)),
                  |C.remainder x jstar e|) := by
  obtain ⟨Kblock, hKblock, h₀, hBlock⟩ :=
    B (1 / 2) Kdens (by norm_num) hKdens
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  intro h hh heven x hx hY hpLarge hweight hmass hLevel
  exact primeDivisorSiftedMass_sum_refined_upper_core C x jstar (Y x)
    θ Kdens (P x) Kblock hKblock h₀ hBlock hx hY hInterval hweight hmass
    (hpPrime x) hpLarge h hh heven hLevel

/-- Combine the proxy extraction with the refined fixed-prime sieve bound. -/
theorem primeBinProxySiftedMass_sieve_upper
    (Q Kblock : ℝ) (hQ : 0 ≤ Q)
    (mass product reciprocal remainder proxyMass primeMass : ℝ)
    (hProxy : proxyMass ≤ Q * primeMass)
    (hSieve : primeMass ≤ mass * product * reciprocal + Kblock * remainder) :
    proxyMass ≤ Q * mass * product * reciprocal + Q * Kblock * remainder := by
  calc
    proxyMass ≤ Q * primeMass := hProxy
    _ ≤ Q * (mass * product * reciprocal + Kblock * remainder) :=
      mul_le_mul_of_nonneg_left hSieve hQ
    _ = Q * mass * product * reciprocal + Q * Kblock * remainder := by ring

/-- A finite family of Type II box errors contributes at most its cardinality
times the per-box saving. -/
theorem abs_sum_le_card_mul_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ a ∈ s, |f a| ≤ E) :
    |∑ a ∈ s, f a| ≤ (s.card : ℝ) * E := by
  calc
    |∑ a ∈ s, f a| ≤ ∑ a ∈ s, |f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ s, E := Finset.sum_le_sum fun a ha => hf a ha
    _ = (s.card : ℝ) * E := by simp [mul_comm]

/-- Mertens' product limit and the shifted singular-series limit give a
positive lower bound for the shifted sieve product. -/
theorem eventually_shiftedSieveProduct_log_lower
    (hc : ClassicalInputs) (hp : ProxyInputs) (b ε : ℝ)
    (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (Real.exp (-Real.eulerMascheroniConstant) * singularSeries) / b - ε ≤
        Analytic.L x * shiftedSieveProduct (x ^ b) := by
  have hxpow : Tendsto (fun x : ℝ => x ^ b) atTop atTop := tendsto_rpow_atTop hb
  have hmertens := hc.mertens.2.comp hxpow
  have hshift := hp.products.2.comp hxpow
  have hprod := hmertens.mul hshift
  have hlimit : 0 < Real.exp (-Real.eulerMascheroniConstant) * singularSeries :=
    mul_pos (Real.exp_pos _) hp.products.1
  have hprodLower : ∀ᶠ x : ℝ in atTop,
      Real.exp (-Real.eulerMascheroniConstant) * singularSeries - b * ε <
        (Real.log (x ^ b) * sieveProduct (x ^ b)) *
          (shiftedSieveProduct (x ^ b) / sieveProduct (x ^ b)) :=
    hprod.eventually (Ioi_mem_nhds (by nlinarith [mul_pos hb hε]))
  have hbasePos : ∀ᶠ x : ℝ in atTop,
      0 < Real.log (x ^ b) * sieveProduct (x ^ b) :=
    hmertens.eventually (Ioi_mem_nhds (Real.exp_pos _))
  have hy : ∀ᶠ x : ℝ in atTop, 1 < x ^ b :=
    hxpow.eventually (eventually_gt_atTop 1)
  filter_upwards [hprodLower, hbasePos, hy, eventually_gt_atTop (1 : ℝ)]
    with x hprodLower hbasePos hyx hx
  have hlogy : 0 < Real.log (x ^ b) := Real.log_pos hyx
  have hVpos : 0 < sieveProduct (x ^ b) := by
    by_contra hnot
    have hVnonpos : sieveProduct (x ^ b) ≤ 0 := le_of_not_gt hnot
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hlogy.le hVnonpos)) hbasePos
  have hcancel :
      (Real.log (x ^ b) * sieveProduct (x ^ b)) *
          (shiftedSieveProduct (x ^ b) / sieveProduct (x ^ b)) =
        Real.log (x ^ b) * shiftedSieveProduct (x ^ b) := by
    field_simp [ne_of_gt hVpos]
  rw [hcancel] at hprodLower
  have hlog : Real.log (x ^ b) = b * Real.log x := Real.log_rpow (by linarith) b
  rw [hlog] at hprodLower
  have hscaled := mul_lt_mul_of_pos_right hprodLower (inv_pos.mpr hb)
  have hleft :
      (Real.exp (-Real.eulerMascheroniConstant) * singularSeries - b * ε) * b⁻¹ =
        Real.exp (-Real.eulerMascheroniConstant) * singularSeries / b - ε := by
    field_simp [ne_of_gt hb]
  have hright :
      (b * Real.log x * shiftedSieveProduct (x ^ b)) * b⁻¹ =
        Real.log x * shiftedSieveProduct (x ^ b) := by
    field_simp [ne_of_gt hb]
  rw [hleft, hright] at hscaled
  exact le_of_lt hscaled

/-- Matching upper bound for the same shifted sieve product. -/
theorem eventually_shiftedSieveProduct_log_upper
    (hc : ClassicalInputs) (hp : ProxyInputs) (b ε : ℝ)
    (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      Analytic.L x * shiftedSieveProduct (x ^ b) ≤
        (Real.exp (-Real.eulerMascheroniConstant) * singularSeries) / b + ε := by
  have hxpow : Tendsto (fun x : ℝ => x ^ b) atTop atTop := tendsto_rpow_atTop hb
  have hmertens := hc.mertens.2.comp hxpow
  have hshift := hp.products.2.comp hxpow
  have hprod := hmertens.mul hshift
  have hlimit : 0 < Real.exp (-Real.eulerMascheroniConstant) * singularSeries :=
    mul_pos (Real.exp_pos _) hp.products.1
  have hprodUpper : ∀ᶠ x : ℝ in atTop,
      (Real.log (x ^ b) * sieveProduct (x ^ b)) *
          (shiftedSieveProduct (x ^ b) / sieveProduct (x ^ b)) <
        Real.exp (-Real.eulerMascheroniConstant) * singularSeries + b * ε :=
    hprod.eventually (Iio_mem_nhds (by nlinarith [mul_pos hb hε]))
  have hbasePos : ∀ᶠ x : ℝ in atTop,
      0 < Real.log (x ^ b) * sieveProduct (x ^ b) :=
    hmertens.eventually (Ioi_mem_nhds (Real.exp_pos _))
  have hy : ∀ᶠ x : ℝ in atTop, 1 < x ^ b :=
    hxpow.eventually (eventually_gt_atTop 1)
  filter_upwards [hprodUpper, hbasePos, hy, eventually_gt_atTop (1 : ℝ)]
    with x hprodUpper hbasePos hyx hx
  have hlogy : 0 < Real.log (x ^ b) := Real.log_pos hyx
  have hVpos : 0 < sieveProduct (x ^ b) := by
    by_contra hnot
    have hVnonpos : sieveProduct (x ^ b) ≤ 0 := le_of_not_gt hnot
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hlogy.le hVnonpos)) hbasePos
  have hcancel :
      (Real.log (x ^ b) * sieveProduct (x ^ b)) *
          (shiftedSieveProduct (x ^ b) / sieveProduct (x ^ b)) =
        Real.log (x ^ b) * shiftedSieveProduct (x ^ b) := by
    field_simp [ne_of_gt hVpos]
  rw [hcancel] at hprodUpper
  have hlog : Real.log (x ^ b) = b * Real.log x := Real.log_rpow (by linarith) b
  rw [hlog] at hprodUpper
  have hscaled := mul_lt_mul_of_pos_right hprodUpper (inv_pos.mpr hb)
  have hleft :
      (Real.exp (-Real.eulerMascheroniConstant) * singularSeries + b * ε) * b⁻¹ =
        Real.exp (-Real.eulerMascheroniConstant) * singularSeries / b + ε := by
    field_simp [ne_of_gt hb]
  have hright :
      (b * Real.log x * shiftedSieveProduct (x ^ b)) * b⁻¹ =
        Real.log x * shiftedSieveProduct (x ^ b) := by
    field_simp [ne_of_gt hb]
  rw [hleft, hright] at hscaled
  exact le_of_lt hscaled

/-- Every squarefree modulus in the odd-prime candidate sieve is odd. -/
theorem candidateSieve_product_modulus_odd (C : CandidateData) (x : ℝ)
    (jstar : ℕ) (y D : ℝ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) {d : ℕ}
    (hd : d ∈ (candidateSieveData C x jstar y hweight hmass).products D) : Odd d := by
  classical
  have hd' : d ∈ (Finset.Icc 1 ⌊D⌋₊).filter
      (fun d => Squarefree d ∧ d.primeFactors ⊆
        (candidateSieveData C x jstar y hweight hmass).primes) := by
    simpa [SieveData.products, candidateSieveData] using hd
  rcases Finset.mem_filter.mp hd' with ⟨hdIcc, hSq, hsubset⟩
  by_contra hodd
  have heven : Even d := Nat.not_odd_iff_even.mp hodd
  have h2dvd : 2 ∣ d := even_iff_two_dvd.mp heven
  have hdpos : d ≠ 0 := by
    have := (Finset.mem_Icc.mp hdIcc).1
    omega
  have h2mem : 2 ∈ d.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero hdpos).2 ⟨Nat.prime_two, h2dvd⟩
  have h2sieve : 2 ∈ (candidateSieveData C x jstar y hweight hmass).primes := hsubset h2mem
  have h2not : 2 ∉ (candidateSieveData C x jstar y hweight hmass).primes := by
    simp [candidateSieveData]
  exact h2not h2sieve

/-- The sieve's remainder sum is covered by the Type I remainder sum once
its cutoff lies below the Type I level. -/
theorem candidateSieve_remainderSum_le_typeI (C : CandidateData) (x : ℝ)
    (jstar : ℕ) (y D θ : ℝ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (hD : D ≤ x ^ θ) :
    (candidateSieveData C x jstar y hweight hmass).remainderSum D ≤
      ∑ d ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d)),
        |C.remainder x jstar d| := by
  classical
  let S := candidateSieveData C x jstar y hweight hmass
  have hsubset : S.products D ⊆
      (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d) := by
    intro d hd
    have hdParts : d ∈ (Finset.Icc 1 ⌊D⌋₊).filter
        (fun d => Squarefree d ∧ d.primeFactors ⊆ S.primes) := by
      simpa [S, SieveData.products, candidateSieveData] using hd
    rcases Finset.mem_filter.mp hdParts with ⟨hdIcc, hSq, hPrimeSubset⟩
    have hdIcc' := Finset.mem_Icc.mp hdIcc
    have hdle : d ≤ ⌊x ^ θ⌋₊ := le_trans hdIcc'.2 (Nat.floor_mono hD)
    have hdOdd : Odd d := candidateSieve_product_modulus_odd C x jstar y D
      hweight hmass (by simpa [S] using hd)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdIcc'.1, hdle⟩, hdOdd, hSq⟩
  rw [SieveData.remainderSum]
  have hsumEq :
      (∑ d ∈ S.products D, |S.remainder d|) =
        ∑ d ∈ S.products D, |C.remainder x jstar d| := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdParts : d ∈ (Finset.Icc 1 ⌊D⌋₊).filter
        (fun d => Squarefree d ∧ d.primeFactors ⊆ S.primes) := by
      simpa [S, SieveData.products, candidateSieveData] using hd
    have hSq : Squarefree d := (Finset.mem_filter.mp hdParts).2.1
    rw [candidateSieve_remainder C x jstar y hweight hmass hSq]
  rw [hsumEq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
  intro d hd hnot
  positivity

/-- Apply the lower approximation from the block sieve to the candidate
survivor mass. -/
theorem candidateSifted_lower (B : BlockSieve) (C : CandidateData) (x : ℝ)
    (jstar : ℕ) (y Kdens : ℝ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar) (hKdens : 0 < Kdens) (hDens :
      (candidateSieveData C x jstar y hweight hmass).densityBounds y (1 / 2) Kdens) :
    ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
      ∀ h : ℕ, h₀ ≤ h → Even h →
        (candidateSieveData C x jstar y hweight hmass).sifted ≥
          (candidateSieveData C x jstar y hweight hmass).X *
              (candidateSieveData C x jstar y hweight hmass).product -
            Kblock * Real.exp (-(h : ℝ)) *
              (candidateSieveData C x jstar y hweight hmass).X *
                (candidateSieveData C x jstar y hweight hmass).product -
            Kblock * (candidateSieveData C x jstar y hweight hmass).remainderSum
              (y ^ (4 * h + 2)) := by
  obtain ⟨Kblock, hKblock, h₀, hB⟩ := B (1 / 2) Kdens (by norm_num) hKdens
  let S := candidateSieveData C x jstar y hweight hmass
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  intro h hh heven
  have hApprox := (hB ℕ S y hDens).2 h hh heven |>.1
  have hlow := (abs_le.mp hApprox).1
  dsimp [S] at hlow ⊢
  linarith

/-- A fixed sieve depth below the Type I exponent stays below its level for
all sufficiently large `x`. -/
theorem eventually_sieve_level_below_typeI (b θ : ℝ) (h : ℕ)
    (hExp : b * (4 * (h : ℝ) + 2) < θ) :
    ∀ᶠ x : ℝ in atTop, (x ^ b) ^ (4 * h + 2) ≤ x ^ θ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hpow : (x ^ b) ^ (4 * h + 2) = x ^ (b * (4 * (h : ℝ) + 2)) := by
    simpa using (Real.rpow_mul_natCast (by positivity : 0 ≤ x) b (4 * h + 2)).symm
  rw [hpow]
  exact Real.rpow_le_rpow_of_exponent_le hx hExp.le

/-- A fixed power of `W(x)=exp(sqrt(log x))` is eventually smaller than
any prescribed positive power of `x`. -/
theorem eventually_rpow_mul_W_pow_le (γ θ : ℝ) (h : ℕ)
    (hγθ : γ < θ) :
    ∀ᶠ x : ℝ in atTop,
      x ^ γ * Analytic.W x ^ (4 * h + 2) ≤ x ^ θ := by
  let N : ℝ := 4 * (h : ℝ) + 2
  let ε : ℝ := (θ - γ) / (2 * N)
  have hN : 0 < N := by dsimp [N]; positivity
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hExp : γ + ε * N ≤ θ := by
    have hεN : ε * N = (θ - γ) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt hN]
    rw [hεN]
    linarith
  have hWEvent := eventually_W_le_rpow ε hε
  filter_upwards [hWEvent, eventually_ge_atTop (1 : ℝ)] with x hWx hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxnonneg : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 1) hx
  have hWpos : 0 < Analytic.W x := by
    dsimp [Analytic.W]
    exact Real.exp_pos _
  have hWpow : Analytic.W x ^ (4 * h + 2) ≤ (x ^ ε) ^ (4 * h + 2) :=
    pow_le_pow_left₀ hWpos.le hWx _
  have hPowEq : (x ^ ε) ^ (4 * h + 2) = x ^ (ε * N) := by
    have hPowEq' : (x ^ ε) ^ (4 * h + 2) =
        x ^ (ε * (4 * (h : ℝ) + 2)) := by
      simpa using (Real.rpow_mul_natCast (by positivity : 0 ≤ x) ε
        (4 * h + 2)).symm
    simpa [N] using hPowEq'
  calc
    x ^ γ * Analytic.W x ^ (4 * h + 2) ≤
        x ^ γ * (x ^ ε) ^ (4 * h + 2) :=
      mul_le_mul_of_nonneg_left hWpow (Real.rpow_nonneg hxnonneg _)
    _ = x ^ (γ + ε * N) := by
      rw [hPowEq, ← Real.rpow_add hxpos]
    _ ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le hx hExp

/-- The `p*d` modulus of the refined fixed-prime sieve stays below its Type
I level when `p` belongs to a fixed exponent bin below that level. -/
theorem eventually_prime_bin_modulus_level
    (γ' θ : ℝ) (h : ℕ) (hγθ : γ' < θ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ p : ℕ, Nat.Prime p → (p : ℝ) ≤ x ^ γ' →
        ∀ d ∈ smallSieveModuli (Analytic.W x)
            ((Analytic.W x) ^ (4 * h + 2)),
          (p * d : ℝ) ≤ x ^ θ := by
  have hProduct := eventually_rpow_mul_W_pow_le γ' θ h hγθ
  filter_upwards [hProduct, eventually_ge_atTop (1 : ℝ)] with x hProduct hx
  intro p hp hpHi d hd
  have hWpos : 0 < Analytic.W x := by
    dsimp [Analytic.W]
    exact Real.exp_pos _
  have hdIcc : d ∈ Finset.Icc 1
      ⌊(Analytic.W x) ^ (4 * h + 2)⌋₊ := by
    have hd' : d ∈ (Finset.Icc 1
        ⌊(Analytic.W x) ^ (4 * h + 2)⌋₊).filter
          (fun d => Squarefree d ∧ d.primeFactors ⊆
            (primesUpTo (Analytic.W x)).erase 2) := by
      simpa [smallSieveModuli] using hd
    exact (Finset.mem_filter.mp hd').1
  have hdLe : (d : ℝ) ≤ Analytic.W x ^ (4 * h + 2) := by
    calc
      (d : ℝ) ≤ (⌊(Analytic.W x) ^ (4 * h + 2)⌋₊ : ℝ) :=
        Nat.cast_le.mpr (Finset.mem_Icc.mp hdIcc).2
      _ ≤ Analytic.W x ^ (4 * h + 2) :=
        Nat.floor_le (by positivity)
  have hprodCast : (p * d : ℝ) = (p : ℝ) * (d : ℝ) := by norm_num
  have hpCastPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  calc
    (p * d : ℝ) = (p : ℝ) * (d : ℝ) := hprodCast
    _ ≤ x ^ γ' * Analytic.W x ^ (4 * h + 2) := by
      calc
        (p : ℝ) * (d : ℝ) ≤ (p : ℝ) * Analytic.W x ^ (4 * h + 2) :=
          mul_le_mul_of_nonneg_left hdLe hpCastPos.le
        _ ≤ x ^ γ' * Analytic.W x ^ (4 * h + 2) :=
          mul_le_mul_of_nonneg_right hpHi (pow_nonneg hWpos.le _)
    _ ≤ x ^ θ := hProduct

/-- Combine a two-sided product asymptotic with the block-sieve lower bound. -/
theorem sieve_lower_from_product_bounds
    (X P L A b ε κ R εR sifted : ℝ)
    (hX : 0 ≤ X) (hL : 0 < L)
    (hPlo : A / b - ε ≤ L * P) (hPhi : L * P ≤ A / b + ε)
    (hBlock : sifted ≥ X * P - κ * X * P - R)
    (hRem : R ≤ εR * X / L) :
    ((if κ ≤ 1 then (1 - κ) * (A / b - ε)
      else (1 - κ) * (A / b + ε)) - εR) * X / L ≤ sifted := by
  have hPlo' : (A / b - ε) / L ≤ P := by
    apply (div_le_iff₀ hL).2
    nlinarith [hPlo]
  have hPhi' : P ≤ (A / b + ε) / L := by
    apply (le_div_iff₀ hL).2
    nlinarith [hPhi]
  let q := if κ ≤ 1 then (1 - κ) * (A / b - ε) else (1 - κ) * (A / b + ε)
  have hq : q / L ≤ P * (1 - κ) := by
    by_cases hκ1 : κ ≤ 1
    · have hfac : 0 ≤ 1 - κ := by linarith
      have hmul := mul_le_mul_of_nonneg_left hPlo' hfac
      dsimp [q]
      rw [if_pos hκ1]
      calc
        (1 - κ) * (A / b - ε) / L = (1 - κ) * ((A / b - ε) / L) := by ring
        _ ≤ (1 - κ) * P := hmul
        _ = P * (1 - κ) := by ring
    · have hneg : 1 - κ ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonpos_left hPhi' hneg
      dsimp [q]
      rw [if_neg hκ1]
      calc
        (1 - κ) * (A / b + ε) / L = (1 - κ) * ((A / b + ε) / L) := by ring
        _ ≤ (1 - κ) * P := hmul
        _ = P * (1 - κ) := by ring
  have hqX : q / L * X ≤ P * (1 - κ) * X :=
    mul_le_mul_of_nonneg_right hq hX
  have hmain : q * X / L ≤ X * P - κ * X * P := by
    calc
      q * X / L = (q / L) * X := by ring
      _ ≤ P * (1 - κ) * X := hqX
      _ = X * P - κ * X * P := by ring
  dsimp [q] at hmain
  by_cases hκ1 : κ ≤ 1
  · simp only [if_pos hκ1]
    have hmain' : (1 - κ) * (A / b - ε) * X / L ≤ X * P - κ * X * P := by
      simpa [hκ1] using hmain
    calc
      ((1 - κ) * (A / b - ε) - εR) * X / L =
          (1 - κ) * (A / b - ε) * X / L - εR * X / L := by ring
      _ ≤ (1 - κ) * (A / b - ε) * X / L - R := by nlinarith [hRem]
      _ ≤ sifted := by linarith [hmain', hBlock]
  · simp only [if_neg hκ1]
    have hmain' : (1 - κ) * (A / b + ε) * X / L ≤ X * P - κ * X * P := by
      simpa [hκ1] using hmain
    calc
      ((1 - κ) * (A / b + ε) - εR) * X / L =
          (1 - κ) * (A / b + ε) * X / L - εR * X / L := by ring
      _ ≤ (1 - κ) * (A / b + ε) * X / L - R := by nlinarith [hRem]
      _ ≤ sifted := by linarith [hmain', hBlock]

/-- A candidate mass lower bound absorbs a sufficiently strong Type I power
saving into a fixed logarithmic tail. -/
theorem x_log_power_tail_le_mass_log18
    (x L CA D mass : ℝ) (hx : 0 ≤ x) (hL : 1 ≤ L)
    (hD : CA + 18 ≤ D) (hMass : x * L ^ (-CA) ≤ mass) :
    x * L ^ (-D) ≤ mass * L ^ (-18 : ℝ) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hexp : -D ≤ -CA - 18 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hL hexp
  have hsplit : L ^ (-CA - 18) = L ^ (-CA) * L ^ (-18 : ℝ) := by
    rw [show -CA - 18 = -CA + (-18 : ℝ) by ring,
      Real.rpow_add hLpos]
  calc
    x * L ^ (-D) ≤ x * L ^ (-CA - 18) := mul_le_mul_of_nonneg_left hpow hx
    _ = (x * L ^ (-CA)) * L ^ (-18 : ℝ) := by rw [hsplit]; ring
    _ ≤ mass * L ^ (-18 : ℝ) :=
      mul_le_mul_of_nonneg_right hMass (Real.rpow_nonneg hLpos.le _)

/-- A fixed logarithmic `-18` remainder is negligible relative to mass over
one logarithm once its coefficient tends to zero at rate `L^-17`. -/
theorem mass_log18_error_le_mass_div_log
    (A η mass L : ℝ) (hA : A * L ^ (-17 : ℝ) ≤ η)
    (hL : 0 < L) (hmass : 0 ≤ mass) :
    A * mass * L ^ (-18 : ℝ) ≤ η * mass / L := by
  have hpow : L ^ (-17 : ℝ) * L ^ (-1 : ℝ) = L ^ (-18 : ℝ) := by
    calc
      _ = L ^ ((-17 : ℝ) + (-1 : ℝ)) :=
        (Real.rpow_add hL (-17 : ℝ) (-1 : ℝ)).symm
      _ = L ^ (-18 : ℝ) := by congr 1 <;> ring
  have hEq : A * mass * L ^ (-18 : ℝ) =
      (A * L ^ (-17 : ℝ)) * (mass / L) := by
    calc
      _ = A * mass * (L ^ (-17 : ℝ) * L ^ (-1 : ℝ)) := by rw [hpow]
      _ = (A * L ^ (-17 : ℝ)) * (mass / L) := by
        rw [Real.rpow_neg_one]
        field_simp [ne_of_gt hL]
  calc
    A * mass * L ^ (-18 : ℝ) =
        (A * L ^ (-17 : ℝ)) * (mass / L) := hEq
    _ ≤ η * (mass / L) :=
      mul_le_mul_of_nonneg_right hA (div_nonneg hmass hL.le)
    _ = η * mass / L := by ring

/-- Presieve mass lower bound with explicit product and Type I errors. -/
theorem candidate_presieve_lower (hc : ClassicalInputs) (hs : SieveInputs)
    (hp : ProxyInputs) (C : CandidateData) (δ : ℝ)
    (hBounds : C.Bounds δ) (hTypeI : C.TypeI)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (b θ εp εr : ℝ) (hb : 0 < b) (hθ : θ < 1 / 2)
    (hεp : 0 < εp) (hεr : 0 < εr) :
    ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
      ∀ h : ℕ, h₀ ≤ h → Even h → b * (4 * (h : ℝ) + 2) < θ →
        ∀ᶠ x : ℝ in atTop,
          ((if Kblock * Real.exp (-(h : ℝ)) ≤ 1 then
              (1 - Kblock * Real.exp (-(h : ℝ))) *
                (Real.exp (-Real.eulerMascheroniConstant) * singularSeries / b - εp)
            else
              (1 - Kblock * Real.exp (-(h : ℝ))) *
                (Real.exp (-Real.eulerMascheroniConstant) * singularSeries / b + εp)) - εr) *
              C.mass x jstar / Analytic.L x ≤ candidateSiftedMass C x jstar (x ^ b) := by
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩
  let D : ℝ := max 1 (CA + 20)
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hDtail : CA + 18 ≤ D := le_trans (by linarith) (le_max_right _ _)
  obtain ⟨Ktype, hKtype, hTypeIEvent⟩ :=
    hTypeI θ D hθ hDpos jstar hjstar
  obtain ⟨Kdens, hKdens, hInterval⟩ := shifted_prime_density_interval_bound_all hc
  obtain ⟨Kblock, hKblock, h₀, hBlock⟩ :=
    hs.block (1 / 2) Kdens (by norm_num) hKdens
  have hBoundEvent := hBound jstar hjstar
  have hCutEvent (h : ℕ) (hExp : b * (4 * (h : ℝ) + 2) < θ) :
      ∀ᶠ x : ℝ in atTop, (x ^ b) ^ (4 * h + 2) ≤ x ^ θ :=
    eventually_sieve_level_below_typeI b θ h hExp
  have hYEvent : ∀ᶠ x : ℝ in atTop, 1 < x ^ b :=
    (tendsto_rpow_atTop hb).eventually (eventually_gt_atTop 1)
  have hXEvent : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  have hLogEvent : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.L x := by
    simpa [Analytic.L] using (Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  have hProductLower := eventually_shiftedSieveProduct_log_lower hc hp b εp hb hεp
  have hProductUpper := eventually_shiftedSieveProduct_log_upper hc hp b εp hb hεp
  have hTailTendsto : Tendsto
      (fun x : ℝ => 2 * Kblock * Ktype * (Analytic.L x) ^ (-17 : ℝ))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => 2 * Kblock * Ktype) atTop
        (nhds (2 * Kblock * Ktype)) := tendsto_const_nhds
    have hlogpow :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17)).comp Real.tendsto_log_atTop
    simpa [Analytic.L, mul_assoc] using hconst.mul hlogpow
  have hTailEvent : ∀ᶠ x : ℝ in atTop,
      2 * Kblock * Ktype * (Analytic.L x) ^ (-17 : ℝ) < εr :=
    hTailTendsto.eventually (Iio_mem_nhds hεr)
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  intro h hh heven hExp
  have hCutoff := hCutEvent h hExp
  filter_upwards [hBoundEvent, hTypeIEvent, hCutoff, hYEvent, hXEvent, hLogEvent,
    hProductLower, hProductUpper, hTailEvent] with x hData hTypeRem hCut hyx hx hL
      hPlo hPhi hTail
  rcases hData with ⟨hMassLower, hHQLower, hHQUpper, hWeights, hWeightUpper, hSupport⟩
  have hx0 : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  have hLpos : 0 < Analytic.L x := lt_of_lt_of_le zero_lt_one hL
  have hLnonneg : 0 ≤ Analytic.L x := le_of_lt hLpos
  have hMass0 : 0 ≤ C.mass x jstar := by
    apply le_trans ?_ hMassLower
    exact mul_nonneg hx0 (Real.rpow_nonneg hLnonneg _)
  have hDens := candidateSieve_densityBounds_fromInterval C x jstar (x ^ b)
    Kdens hInterval hWeights hMass0 hyx
  let S := candidateSieveData C x jstar (x ^ b) hWeights hMass0
  have hApprox := (hBlock ℕ S (x ^ b) hDens).2 h hh heven |>.1
  have hlow := (abs_le.mp hApprox).1
  have hXeq : S.X = C.mass x jstar := rfl
  have hPeq : S.product = shiftedSieveProduct (x ^ b) :=
    candidateSieve_product C x jstar (x ^ b) hWeights hMass0
  have hSeq : S.sifted = candidateSiftedMass C x jstar (x ^ b) :=
    candidateSieve_sifted_eq C x jstar (x ^ b) hWeights hMass0
  have hBlockLower : candidateSiftedMass C x jstar (x ^ b) ≥
      C.mass x jstar * shiftedSieveProduct (x ^ b) -
        (Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar * shiftedSieveProduct (x ^ b) -
        Kblock * S.remainderSum ((x ^ b) ^ (4 * h + 2)) := by
    have hlow' := hlow
    rw [hSeq, hXeq, hPeq] at hlow'
    linarith [hlow']
  have hRemS := candidateSieve_remainderSum_le_typeI C x jstar (x ^ b)
    ((x ^ b) ^ (4 * h + 2)) θ hWeights hMass0 hCut
  have hRemType : S.remainderSum ((x ^ b) ^ (4 * h + 2)) ≤
      Ktype * (x * (Analytic.L x) ^ (-D) + C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ)) := by
    dsimp [S]
    exact le_trans hRemS hTypeRem
  have hMassTail := x_log_power_tail_le_mass_log18 x (Analytic.L x) CA D
    (C.mass x jstar) hx0 hL hDtail hMassLower
  have hSumTail : x * (Analytic.L x) ^ (-D) +
      C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ) ≤
        2 * C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ) := by
    linarith [hMassTail]
  have hTypeRem' := mul_le_mul_of_nonneg_left hSumTail hKtype.le
  have hRemBlock : Kblock * S.remainderSum ((x ^ b) ^ (4 * h + 2)) ≤
      εr * C.mass x jstar / Analytic.L x := by
    have hpowRel : (Analytic.L x) ^ (-18 : ℝ) * Analytic.L x =
        (Analytic.L x) ^ (-17 : ℝ) := by
      calc
        (Analytic.L x) ^ (-18 : ℝ) * Analytic.L x =
            (Analytic.L x) ^ (-18 : ℝ) * (Analytic.L x) ^ (1 : ℝ) := by simp
        _ = (Analytic.L x) ^ ((-18 : ℝ) + 1) :=
          (Real.rpow_add hLpos (-18 : ℝ) 1).symm
        _ = (Analytic.L x) ^ (-17 : ℝ) := by congr 1 <;> ring
    have hpowInv : (Analytic.L x) ^ (-18 : ℝ) =
        (Analytic.L x) ^ (-17 : ℝ) * (Analytic.L x)⁻¹ := by
      calc
        _ = ((Analytic.L x) ^ (-18 : ℝ) * Analytic.L x) * (Analytic.L x)⁻¹ := by
          field_simp [ne_of_gt hLpos]
        _ = (Analytic.L x) ^ (-17 : ℝ) * (Analytic.L x)⁻¹ := by rw [hpowRel]
    have hcoeffEq :
        2 * Kblock * Ktype * (Analytic.L x) ^ (-18 : ℝ) * C.mass x jstar =
          (2 * Kblock * Ktype * (Analytic.L x) ^ (-17 : ℝ)) *
            (C.mass x jstar / Analytic.L x) := by
      rw [hpowInv]
      field_simp [ne_of_gt hLpos]
    calc
      Kblock * S.remainderSum ((x ^ b) ^ (4 * h + 2)) ≤
          Kblock * (Ktype * (x * (Analytic.L x) ^ (-D) +
            C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ))) :=
        mul_le_mul_of_nonneg_left hRemType hKblock.le
      _ ≤ Kblock * (Ktype * (2 * C.mass x jstar * (Analytic.L x) ^ (-18 : ℝ))) :=
        mul_le_mul_of_nonneg_left hTypeRem' hKblock.le
      _ = 2 * Kblock * Ktype * (Analytic.L x) ^ (-18 : ℝ) * C.mass x jstar := by ring
      _ = (2 * Kblock * Ktype * (Analytic.L x) ^ (-17 : ℝ)) *
            (C.mass x jstar / Analytic.L x) := hcoeffEq
      _ ≤ εr * (C.mass x jstar / Analytic.L x) :=
        mul_le_mul_of_nonneg_right hTail.le (div_nonneg hMass0 hLpos.le)
      _ = εr * C.mass x jstar / Analytic.L x := by ring
  exact sieve_lower_from_product_bounds (C.mass x jstar) (shiftedSieveProduct (x ^ b))
    (Analytic.L x) (Real.exp (-Real.eulerMascheroniConstant) * singularSeries)
    b εp (Kblock * Real.exp (-(h : ℝ)))
    (Kblock * S.remainderSum ((x ^ b) ^ (4 * h + 2))) εr
    (candidateSiftedMass C x jstar (x ^ b))
    hMass0 hLpos hPlo hPhi hBlockLower hRemBlock

/-- Choose the presieve exponent and even sieve depth in the range where the
Type I level holds and the block-sieve error is small relative to `b`. -/
theorem choose_presieve_depth (θ Kblock : ℝ) (h₀ : ℕ) (ε : ℝ)
    (hθ : 0 < θ) (hK : 0 < Kblock) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∃ h : ℕ, h₀ ≤ h ∧ Even h ∧
      b * (4 * (h : ℝ) + 2) < θ ∧ Kblock * Real.exp (-(h : ℝ)) / b < ε := by
  have hNatExp : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ)))
      atTop (nhds 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    · funext n
      simp [pow_one]
  have hErrorTendsto : Tendsto
      (fun n : ℕ => (100 * Kblock / θ) * ((n : ℝ) * Real.exp (-(n : ℝ))))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hNatExp)
  have hError : ∀ᶠ n : ℕ in atTop,
      (100 * Kblock / θ) * ((n : ℝ) * Real.exp (-(n : ℝ))) < ε :=
    hErrorTendsto.eventually (Iio_mem_nhds hε)
  have hLarge : ∀ᶠ n : ℕ in atTop, h₀ ≤ n := eventually_ge_atTop h₀
  have hPos : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n, ⟨⟨hnErr, hnLarge⟩, hnPos⟩⟩ := (hError.and hLarge |>.and hPos).exists
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnPos
  let b : ℝ := θ / (100 * (n : ℝ))
  let h : ℕ := 2 * n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hnPos
  have hb : 0 < b := by dsimp [b]; exact div_pos hθ (by positivity)
  have hCut : b * (4 * (h : ℝ) + 2) < θ := by
    have hfrac : (8 * (n : ℝ) + 2) / (100 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith [hnR1]
    dsimp [b, h]
    push_cast
    calc
      θ / (100 * (n : ℝ)) * (4 * (2 * (n : ℝ)) + 2) =
          θ * ((8 * (n : ℝ) + 2) / (100 * (n : ℝ))) := by ring
      _ < θ := by simpa using mul_lt_mul_of_pos_left hfrac hθ
  have hErrorFinal : Kblock * Real.exp (-(h : ℝ)) / b < ε := by
    have hexp : Real.exp (-(2 * (n : ℝ))) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hnR]
    have hbound := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ (n : ℝ))
    have hconst : 100 * Kblock / θ > 0 := div_pos (by positivity) hθ
    calc
      Kblock * Real.exp (-(h : ℝ)) / b =
          (100 * Kblock / θ) * ((n : ℝ) * Real.exp (-(2 * (n : ℝ)))) := by
            dsimp [h, b]
            push_cast
            field_simp [ne_of_gt hθ, ne_of_gt hnR]
            <;> ring
      _ ≤ (100 * Kblock / θ) * ((n : ℝ) * Real.exp (-(n : ℝ))) :=
            mul_le_mul_of_nonneg_left hbound hconst.le
      _ < ε := hnErr
  refine ⟨b, hb, h, ?_, ?_, hCut, hErrorFinal⟩
  · dsimp [h]
    omega
  · exact ⟨n, by omega⟩

/-- Choose the small presieve exponent and sieve depth together with the
rough-density error required later by the least-factor subtraction. -/
theorem choose_presieve_parameters (hp : ProxyInputs) (θ Kblock : ℝ) (h₀ : ℕ)
    (εs εd : ℝ) (hθ : 0 < θ) (hK : 0 < Kblock)
    (hεs : 0 < εs) (hεd : 0 < εd) :
    ∃ b c K b₀ : ℝ, ∃ hdepth : ℕ,
      0 < b ∧ b < b₀ ∧ 0 < c ∧ 0 < K ∧ 0 < b₀ ∧
      h₀ ≤ hdepth ∧ Even hdepth ∧
      b * (4 * (hdepth : ℝ) + 2) < θ ∧
      Kblock * Real.exp (-(hdepth : ℝ)) / b < εs ∧
      K * Real.exp (-c / b) / b < εd ∧
      roughDensity b 1 ≤
        Real.exp (-Real.eulerMascheroniConstant) / b +
          Real.exp (-Real.eulerMascheroniConstant) * εd := by
  obtain ⟨c, K, b₀, hc, hKdens, hb₀, hDensity⟩ := hp.identities.2.2
  have hNatExp : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ)))
      atTop (nhds 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    · funext n
      simp [pow_one]
  have hSieveErr : Tendsto
      (fun n : ℕ => (100 * Kblock / θ) * ((n : ℝ) * Real.exp (-(n : ℝ))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hNatExp
  let q : ℝ := 100 * c / θ
  have hq : 0 < q := by dsimp [q]; positivity
  have hQatTop : Tendsto (fun n : ℕ => q * n) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hq).2 tendsto_natCast_atTop_atTop
  have hDensityErr : Tendsto
      (fun n : ℕ => (K / c) * ((q * n) * Real.exp (-(q * n))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hQatTop)
  have hSieveSmall : ∀ᶠ n : ℕ in atTop,
      (100 * Kblock / θ) * ((n : ℝ) * Real.exp (-(n : ℝ))) < εs :=
    hSieveErr.eventually (Iio_mem_nhds hεs)
  have hDensitySmall : ∀ᶠ n : ℕ in atTop,
      (K / c) * ((q * n) * Real.exp (-(q * n))) < εd :=
    hDensityErr.eventually (Iio_mem_nhds hεd)
  have hbSmall : ∀ᶠ n : ℕ in atTop, θ / (100 * (n : ℝ)) < b₀ := by
    have hlarge : ∀ᶠ n : ℕ in atTop, θ / (100 * b₀) < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (θ / (100 * b₀)))
    filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    rw [div_lt_iff₀ (by positivity : 0 < 100 * (n : ℝ))]
    rw [div_lt_iff₀ (by positivity : 0 < 100 * b₀)] at hn
    nlinarith
  have hDepthLarge : ∀ᶠ n : ℕ in atTop, h₀ ≤ 2 * n := by
    exact (eventually_ge_atTop h₀).mono fun n hn => hn.trans (by omega)
  have hnPos : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n, ⟨⟨⟨⟨hnS, hnD⟩, hnB⟩, hnH⟩, hn1⟩⟩ :=
    (hSieveSmall.and hDensitySmall |>.and hbSmall |>.and hDepthLarge |>.and hnPos).exists
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  let b : ℝ := θ / (100 * (n : ℝ))
  let hdepth : ℕ := 2 * n
  have hb : 0 < b := by dsimp [b]; positivity
  have hCut : b * (4 * (hdepth : ℝ) + 2) < θ := by
    have hfrac : (8 * (n : ℝ) + 2) / (100 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      nlinarith [hnR1]
    dsimp [b, hdepth]
    push_cast
    calc
      θ / (100 * (n : ℝ)) * (4 * (2 * (n : ℝ)) + 2) =
          θ * ((8 * (n : ℝ) + 2) / (100 * (n : ℝ))) := by ring
      _ < θ := by simpa using mul_lt_mul_of_pos_left hfrac hθ
  have hSieveBound : Kblock * Real.exp (-(hdepth : ℝ)) / b < εs := by
    have hexp : Real.exp (-(2 * (n : ℝ))) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hnR]
    have hbound := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ (n : ℝ))
    have hconst : 0 < 100 * Kblock / θ := by positivity
    calc
      Kblock * Real.exp (-(hdepth : ℝ)) / b =
          (100 * Kblock / θ) * ((n : ℝ) * Real.exp (-(2 * (n : ℝ)))) := by
            dsimp [hdepth, b]
            push_cast
            field_simp [ne_of_gt hθ, ne_of_gt hnR]
            <;> ring
      _ ≤ (100 * Kblock / θ) * ((n : ℝ) * Real.exp (-(n : ℝ))) :=
        mul_le_mul_of_nonneg_left hbound hconst.le
      _ < εs := hnS
  have hDensityBound : K * Real.exp (-c / b) / b < εd := by
    have hqEq : c / b = q * n := by
      dsimp [b, q]
      field_simp [ne_of_gt hθ, ne_of_gt hnR]
    have hnegEq : -c / b = -(q * n) := by
      calc
        -c / b = -(c / b) := by ring
        _ = -(q * n) := congrArg Neg.neg hqEq
    have hEq : K * Real.exp (-c / b) / b = (K / c) * ((q * n) * Real.exp (-(q * n))) := by
      rw [hnegEq]
      dsimp [b, q]
      field_simp [ne_of_gt hc, ne_of_gt hθ, ne_of_gt hnR]
    rw [hEq]
    exact hnD
  have hbb₀ : b < b₀ := by simpa [b] using hnB
  have hDensityAtB := hDensity b hb hbb₀
  have hE : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  have hRough : roughDensity b 1 ≤
      Real.exp (-Real.eulerMascheroniConstant) / b +
        Real.exp (-Real.eulerMascheroniConstant) * εd := by
    calc
      roughDensity b 1 ≤
          Real.exp (-Real.eulerMascheroniConstant) / b *
            (1 + K * Real.exp (-c / b)) := hDensityAtB
      _ = Real.exp (-Real.eulerMascheroniConstant) / b +
          Real.exp (-Real.eulerMascheroniConstant) *
            (K * Real.exp (-c / b) / b) := by ring
      _ ≤ Real.exp (-Real.eulerMascheroniConstant) / b +
          Real.exp (-Real.eulerMascheroniConstant) * εd := by
        nlinarith [mul_le_mul_of_nonneg_left hDensityBound.le hE.le]
  refine ⟨b, c, K, b₀, hdepth, hb, hbb₀, hc, hKdens, hb₀,
    ?_, ?_, hCut, hSieveBound, hDensityBound, hRough⟩
  · simpa [hdepth] using hnH
  · dsimp [hdepth]
    exact ⟨n, by omega⟩

/-- Finite set form of the final subtraction: classify each sifted composite
as belonging to one of the two error classes. -/
theorem prime_sum_ge_sifted_sub_errors
    {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℝ)
    (isPrime survives unbalanced balanced : α → Prop)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hcover : ∀ a ∈ s, survives a → ¬ isPrime a →
      unbalanced a ∨ balanced a) :
    (∑ a ∈ (s.filter survives), w a) ≤
      (∑ a ∈ (s.filter isPrime), w a) +
        (∑ a ∈ (s.filter unbalanced), w a) +
        ∑ a ∈ (s.filter balanced), w a := by
  classical
  calc
    (∑ a ∈ (s.filter survives), w a) =
        ∑ a ∈ s, (if survives a then w a else 0) := by
      simp only [Finset.sum_filter]
    _ ≤ ∑ a ∈ s,
        ((if isPrime a then w a else 0) +
          (if unbalanced a then w a else 0) +
          (if balanced a then w a else 0)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hwa : 0 ≤ w a := hw a ha
      have hp0 : 0 ≤ (if isPrime a then w a else 0) := by
        split_ifs <;> positivity
      have hu0 : 0 ≤ (if unbalanced a then w a else 0) := by
        split_ifs <;> positivity
      have hb0 : 0 ≤ (if balanced a then w a else 0) := by
        split_ifs <;> positivity
      by_cases hs : survives a
      · by_cases hp : isPrime a
        · simp [hs, hp]
          linarith
        · rcases hcover a ha hs hp with hu | hb
          · simp [hs, hp, hu]
            linarith
          · simp [hs, hp, hb]
            linarith
      · simp [hs]
        linarith
    _ = (∑ a ∈ (s.filter isPrime), w a) +
          (∑ a ∈ (s.filter unbalanced), w a) +
          ∑ a ∈ (s.filter balanced), w a := by
      simp only [Finset.sum_filter, Finset.sum_add_distrib]

/-- The exceptional rough slot can be placed far enough down the geometric
sequence after the earlier candidate choices have been fixed. -/
theorem exists_late_slot (C : CandidateData) (δ b : ℝ)
    (hC : C.Geometry δ) (hb : 0 < b) :
    ∃ jstar : ℕ, C.j₀ ≤ jstar ∧
      C.bands.c₂ * C.bands.s' * (1 / 2 : ℝ) ^ jstar < b / 12 := by
  have hc₂ : 0 < C.bands.c₂ := lt_trans hC.1.2.1 hC.1.2.2.1
  have hs' : 0 < C.bands.s' := hC.1.2.2.2.1
  have hc : 0 < C.bands.c₂ * C.bands.s' := mul_pos hc₂ hs'
  have hpow : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) ^ j < (b / 12) / (C.bands.c₂ * C.bands.s') :=
    hpow.eventually (Iio_mem_nhds (div_pos (div_pos hb (by norm_num)) hc))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨max C.j₀ N, le_max_left _ _, ?_⟩
  have hj : N ≤ max C.j₀ N := le_max_right _ _
  have hlt := hN (max C.j₀ N) hj
  calc
    C.bands.c₂ * C.bands.s' * (1 / 2 : ℝ) ^ max C.j₀ N <
        C.bands.c₂ * C.bands.s' * ((b / 12) / (C.bands.c₂ * C.bands.s')) :=
      mul_lt_mul_of_pos_left hlt hc
    _ = b / 12 := by field_simp

/-- Choose the balance window only after its uniform constant is known. -/
theorem choose_kappa (singularSeries Kbal : ℝ)
    (hS : 0 < singularSeries) (hK : 0 < Kbal) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 / 50 ∧ Kbal * κ < singularSeries / 4 := by
  let κ := min (1 / 100 : ℝ) (singularSeries / (8 * Kbal))
  have hκ : 0 < κ := lt_min (by norm_num) (div_pos hS (by positivity))
  refine ⟨κ, hκ, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · calc
      Kbal * κ ≤ Kbal * (singularSeries / (8 * Kbal)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
      _ = singularSeries / 8 := by field_simp
      _ < singularSeries / 4 := by linarith

/-- The density error from the rough-number upper bound vanishes as the
presieve exponent tends to zero. -/
theorem choose_small_exponent (c K b₀ ε : ℝ)
    (hc : 0 < c) (_hK : 0 < K) (hb₀ : 0 < b₀) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ b < b₀ ∧ K * Real.exp (-c / b) / b < ε := by
  have hscaled : Tendsto (fun R : ℝ => (K / c) * (R * Real.exp (-R))) atTop (nhds 0) := by
    simpa [pow_one, mul_assoc] using
      tendsto_const_nhds.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  have hsmall : ∀ᶠ R : ℝ in atTop,
      (K / c) * (R * Real.exp (-R)) < ε :=
    hscaled.eventually (Iio_mem_nhds hε)
  have hlarge : ∀ᶠ R : ℝ in atTop, c / b₀ < R := eventually_gt_atTop (c / b₀)
  obtain ⟨R, hRsmall, hRlarge⟩ := (hsmall.and hlarge).exists
  have hRpos : 0 < R := lt_trans (div_pos hc hb₀) hRlarge
  refine ⟨c / R, div_pos hc hRpos, ?_, ?_⟩
  · rw [div_lt_iff₀ hRpos]
    simpa [mul_comm] using (div_lt_iff₀ hb₀).mp hRlarge
  · have htarget : K * Real.exp (-c / (c / R)) / (c / R) =
        (K / c) * (R * Real.exp (-R)) := by
      rw [show -c / (c / R) = -R by field_simp]
      field_simp [hc.ne', hRpos.ne']
    rw [htarget]
    exact hRsmall

/-- The proxy density input supplies a small exponent with a controlled
absolute error in the rough-number density bound. -/
theorem choose_density_exponent (hp : ProxyInputs) (ε : ℝ) (hε : 0 < ε) :
    ∃ b c K b₀ : ℝ, 0 < b ∧ b < b₀ ∧ 0 < c ∧ 0 < K ∧ 0 < b₀ ∧
      roughDensity b 1 ≤
        Real.exp (-Real.eulerMascheroniConstant) / b +
          Real.exp (-Real.eulerMascheroniConstant) * ε := by
  obtain ⟨c, K, b₀, hc, hK, hb₀, hDensity⟩ := hp.identities.2.2
  obtain ⟨b, hb, hbb₀, herr⟩ := choose_small_exponent c K b₀ ε hc hK hb₀ hε
  refine ⟨b, c, K, b₀, hb, hbb₀, hc, hK, hb₀, ?_⟩
  have hrough := hDensity b hb hbb₀
  have hE : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  calc
    roughDensity b 1 ≤
        Real.exp (-Real.eulerMascheroniConstant) / b *
          (1 + K * Real.exp (-c / b)) := hrough
    _ = Real.exp (-Real.eulerMascheroniConstant) / b +
          Real.exp (-Real.eulerMascheroniConstant) *
            (K * Real.exp (-c / b) / b) := by ring
    _ ≤ Real.exp (-Real.eulerMascheroniConstant) / b +
          Real.exp (-Real.eulerMascheroniConstant) * ε := by
      nlinarith [mul_le_mul_of_nonneg_left herr.le hE.le]

/-- Below twice the cutoff, a rough integer can only contribute its
one-prime term to the formal rough density. -/
theorem roughDensity_eq_inv_of_lt_two (γ w : ℝ) (hγ : 0 < γ)
    (hw : 0 ≤ w) (hwγ : w < 2 * γ) :
    roughDensity γ w = 1 / w := by
  have hratio : w / γ < 2 := (div_lt_iff₀ hγ).2 (by nlinarith)
  have hfloor : (⌊w / γ⌋₊ : ℝ) ≤ w / γ := Nat.floor_le (by positivity)
  have hempty : Finset.Icc 2 ⌊w / γ⌋₊ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hl).1
    have hlf : (l : ℝ) ≤ (⌊w / γ⌋₊ : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hl).2
    linarith
  simp [roughDensity, hempty]

/-- The explicit Buchstab density is nonnegative in its natural range. -/
theorem roughDensity_nonneg (γ w : ℝ) (hγ : 0 < γ) (hw : 0 < w) :
    0 ≤ roughDensity γ w := by
  have hterm (l : ℕ) : 0 ≤ densityTerm γ w l := by
    unfold densityTerm
    apply MeasureTheory.integral_nonneg
    intro t
    change 0 ≤ if (∀ i, γ ≤ t i) ∧ (∑ i, t i) ≤ w - γ then
      (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0
    by_cases hdom : (∀ i, γ ≤ t i) ∧ (∑ i, t i) ≤ w - γ
    · have hden : 0 < w - ∑ i, t i := by linarith [hdom.2]
      have ht : ∀ i, 0 < t i := fun i => lt_of_lt_of_le hγ (hdom.1 i)
      simp [hdom]
      have hprod : 0 < ∏ i, t i := by
        apply Finset.prod_pos
        intro i hi
        exact ht i
      exact le_of_lt (mul_pos (inv_pos.mpr hden) (inv_pos.mpr hprod))
    · simp [hdom]
  unfold roughDensity
  apply add_nonneg (inv_nonneg.mpr hw.le)
  apply Finset.sum_nonneg
  intro l hl
  exact div_nonneg (hterm l) (by positivity)

def densityMeshPoint (b κ : ℝ) (N i : ℕ) : ℝ :=
  b + ((1 / 2 : ℝ) - κ - b) * ((i : ℝ) / (N : ℝ))

def densityMeshSup (b κ : ℝ) (N i : ℕ) : ℝ :=
  sSup ((fun a : ℝ => roughDensity (densityMeshPoint b κ N i) (1 - a)) ''
    Set.Icc (densityMeshPoint b κ N i) (densityMeshPoint b κ N (i + 1)))

set_option maxHeartbeats 1000000 in
/-- Uniform continuity turns the rough-cofactor bin suprema into an upper
Riemann sum for the least-factor density integral. -/
theorem density_mesh_integral_bound (hp : ProxyInputs) (b κ ε : ℝ)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hbκ : b < κ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i < N, 0 ≤ densityMeshSup b κ N i) ∧
      (∑ i ∈ Finset.range N,
        (densityMeshSup b κ N i +
          ε / (2 * (Real.log (((1 / 2 : ℝ) - κ) / b) + 1))) *
            Real.log (densityMeshPoint b κ N (i + 1) /
              densityMeshPoint b κ N i)) ≤ roughDensity b 1 - 1 + ε := by
  let top : ℝ := (1 / 2 : ℝ) - κ
  let width : ℝ := top - b
  let logRange : ℝ := Real.log (top / b)
  let η : ℝ := ε / (2 * (logRange + 1))
  have htoppos : 0 < top := by dsimp [top]; linarith [hκsmall]
  have htoplt : top < 1 / 2 := by dsimp [top]; linarith [hκ]
  have hbtop : b < top := by
    dsimp [top]
    nlinarith [hκsmall, hbκ]
  have hwidth : 0 < width := by dsimp [width]; linarith
  have hlogRange : 0 < logRange := by
    dsimp [logRange]
    apply Real.log_pos
    exact (one_lt_div hb).2 hbtop
  have hη : 0 < η := by
    dsimp [η]
    positivity
  let K : Set (ℝ × ℝ) := Set.Icc b top ×ˢ Set.Icc b top
  let F : ℝ × ℝ → ℝ := fun z => roughDensity z.1 (1 - z.2)
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.prod isCompact_Icc
  have hFcont : ContinuousOn F K := by
    have hmap : ContinuousOn (fun z : ℝ × ℝ => (z.1, 1 - z.2)) K := by
      fun_prop
    have hmaps : Set.MapsTo (fun z : ℝ × ℝ => (z.1, 1 - z.2)) K
        {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2} := by
      intro z hz
      rcases z with ⟨g, a⟩
      simp only [K, Set.mem_prod, Set.mem_Icc] at hz
      change 0 < g ∧ g < 1 - a
      constructor
      · exact lt_of_lt_of_le hb hz.1.1
      · have hg : g < 1 / 2 := lt_of_le_of_lt hz.1.2 htoplt
        have ha : 1 / 2 < 1 - a := by
          have : a < 1 / 2 := lt_of_le_of_lt hz.2.2 htoplt
          linarith
        exact lt_trans hg ha
    have h := hp.identities.1.comp' hmap hmaps
    simpa [F, Function.comp_def] using h
  have hFuc : UniformContinuousOn F K := hKcompact.uniformContinuousOn_of_continuous hFcont
  obtain ⟨δm, hδm, hclose⟩ :=
    (Metric.uniformContinuousOn_iff.mp hFuc) (η / 2) (by positivity)
  have hδmpos : 0 < δm := hδm
  let N : ℕ := ⌈width / δm⌉₊ + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hratioCeil : width / δm ≤ (⌈width / δm⌉₊ : ℝ) := Nat.le_ceil _
  have hratioN : width / δm < (N : ℝ) := by
    dsimp [N]
    push_cast
    linarith
  have hwidthMul : width < δm * (N : ℝ) :=
    by nlinarith [(div_lt_iff₀ hδmpos).1 hratioN]
  have hstepSmall : width / (N : ℝ) < δm := by
    apply (div_lt_iff₀ hNR).2
    nlinarith [hwidthMul]
  have hPointBounds (i : ℕ) (hi : i ≤ N) :
      b ≤ densityMeshPoint b κ N i ∧ densityMeshPoint b κ N i ≤ top := by
    have hiR : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    have hratio0 : 0 ≤ (i : ℝ) / (N : ℝ) := div_nonneg (by positivity) hNR.le
    have hratio1 : (i : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hNR]
      simpa using hiR
    have hcoef : 0 ≤ (1 / 2 : ℝ) - κ - b := by
      dsimp [top] at hbtop ⊢
      linarith
    constructor
    · dsimp [densityMeshPoint, width, top]
      nlinarith [mul_nonneg hcoef hratio0]
    · dsimp [densityMeshPoint, width, top]
      have hmul := mul_le_mul_of_nonneg_left hratio1 hcoef
      nlinarith
  have hpoint0 : densityMeshPoint b κ N 0 = b := by
    simp [densityMeshPoint]
  have hpointN : densityMeshPoint b κ N N = top := by
    have hNN : (N : ℝ) ≠ 0 := ne_of_gt hNR
    dsimp [densityMeshPoint, width, top]
    field_simp [hNN]
    <;> ring
  have hStep (i : ℕ) :
      densityMeshPoint b κ N (i + 1) - densityMeshPoint b κ N i =
        width / (N : ℝ) := by
    dsimp [densityMeshPoint, width, top]
    push_cast
    ring
  let G : ℝ → ℝ := fun a => F (a, a)
  let H : ℝ → ℝ := fun a => G a / a
  have hdiagCont : ContinuousOn G (Set.Icc b top) := by
    have hdiag : ContinuousOn (fun a : ℝ => (a, a)) (Set.Icc b top) := by
      fun_prop
    have hdiagMaps : Set.MapsTo (fun a : ℝ => (a, a)) (Set.Icc b top) K := by
      intro a ha
      change a ∈ Set.Icc b top ∧ a ∈ Set.Icc b top
      exact ⟨ha, ha⟩
    have h := hFcont.comp' hdiag hdiagMaps
    simpa [G, Function.comp_def] using h
  have hHcont : ContinuousOn H (Set.Icc b top) := by
    apply hdiagCont.div continuousOn_id
    intro a ha
    exact ne_of_gt (lt_of_lt_of_le hb ha.1)
  have hHint : ∀ i < N,
      IntervalIntegrable H MeasureTheory.volume
        (densityMeshPoint b κ N i) (densityMeshPoint b κ N (i + 1)) := by
    intro i hi
    have hiN : i + 1 ≤ N := by omega
    have hleft := hPointBounds i (Nat.le_of_lt hi)
    have hright := hPointBounds (i + 1) hiN
    have hleftRight : densityMeshPoint b κ N i ≤ densityMeshPoint b κ N (i + 1) := by
      have hstep := hStep i
      have hpos : 0 < width / (N : ℝ) := div_pos hwidth hNR
      linarith
    have hsub : Set.Icc (densityMeshPoint b κ N i)
        (densityMeshPoint b κ N (i + 1)) ⊆ Set.Icc b top := by
      intro a ha
      exact ⟨le_trans hleft.1 ha.1, le_trans ha.2 hright.2⟩
    exact (hHcont.mono hsub).intervalIntegrable_of_Icc hleftRight
  have hEcont : ContinuousOn (fun a : ℝ => 1 / a) (Set.Icc b top) := by
    apply continuousOn_const.div continuousOn_id
    intro a ha
    exact ne_of_gt (lt_of_lt_of_le hb ha.1)
  have hEhint : ∀ i < N,
      IntervalIntegrable (fun a : ℝ => 1 / a) MeasureTheory.volume
        (densityMeshPoint b κ N i) (densityMeshPoint b κ N (i + 1)) := by
    intro i hi
    have hiN : i + 1 ≤ N := by omega
    have hleft := hPointBounds i (Nat.le_of_lt hi)
    have hright := hPointBounds (i + 1) hiN
    have hleftRight : densityMeshPoint b κ N i ≤ densityMeshPoint b κ N (i + 1) := by
      have hstep := hStep i
      have hpos : 0 < width / (N : ℝ) := div_pos hwidth hNR
      linarith
    have hsub : Set.Icc (densityMeshPoint b κ N i)
        (densityMeshPoint b κ N (i + 1)) ⊆ Set.Icc b top := by
      intro a ha
      exact ⟨le_trans hleft.1 ha.1, le_trans ha.2 hright.2⟩
    exact (hEcont.mono hsub).intervalIntegrable_of_Icc hleftRight
  have hBaseInt : IntervalIntegrable H MeasureTheory.volume b top :=
    hHcont.intervalIntegrable_of_Icc (le_of_lt hbtop)
  have hEBaseInt : IntervalIntegrable (fun a : ℝ => 1 / a) MeasureTheory.volume b top :=
    hEcont.intervalIntegrable_of_Icc (le_of_lt hbtop)
  have hsumH :
      (∑ i ∈ Finset.range N,
        ∫ a in densityMeshPoint b κ N i..densityMeshPoint b κ N (i + 1), H a) =
        ∫ a in b..top, H a := by
    simpa [hpoint0, hpointN] using
      (intervalIntegral.sum_integral_adjacent_intervals (f := H) (μ := MeasureTheory.volume)
        (a := fun i => densityMeshPoint b κ N i) (n := N) hHint)
  have hsumE :
      (∑ i ∈ Finset.range N,
        ∫ a in densityMeshPoint b κ N i..densityMeshPoint b κ N (i + 1), 1 / a) =
        ∫ a in b..top, 1 / a := by
    simpa [hpoint0, hpointN] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := fun a : ℝ => 1 / a) (μ := MeasureTheory.volume)
        (a := fun i => densityMeshPoint b κ N i) (n := N) hEhint)
  have hlogBase : (∫ a in b..top, 1 / a) = logRange := by
    dsimp [logRange]
    exact integral_one_div_of_pos hb htoppos
  have hlogsum :
      (∑ i ∈ Finset.range N,
        Real.log (densityMeshPoint b κ N (i + 1) /
          densityMeshPoint b κ N i)) = logRange := by
    calc
      _ = ∑ i ∈ Finset.range N,
          ∫ a in densityMeshPoint b κ N i..densityMeshPoint b κ N (i + 1), 1 / a := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiLt : i < N := Finset.mem_range.mp hi
            have hiN : i + 1 ≤ N := Nat.succ_le_of_lt hiLt
            have hleft := hPointBounds i (Nat.le_of_lt (Finset.mem_range.mp hi))
            have hright := hPointBounds (i + 1) hiN
            exact (integral_one_div_of_pos
              (lt_of_lt_of_le hb hleft.1) (lt_of_lt_of_le hb hright.1)).symm
      _ = ∫ a in b..top, 1 / a := hsumE
      _ = logRange := hlogBase
  have htopTail : top < 1 / 2 := htoplt
  have hTailEq (a : ℝ) (ha : a ∈ Set.Icc top (1 / 2 : ℝ)) :
      H a = 1 / (a * (1 - a)) := by
    have haPos : 0 < a := lt_of_lt_of_le htoppos ha.1
    have hwPos : 0 < 1 - a := by linarith [ha.2]
    have hwNonneg : 0 ≤ 1 - a := hwPos.le
    have hthree : 1 / 3 < a := by
      have htopgt : 12 / 25 < top := by
        dsimp [top]
        nlinarith [hκsmall]
      have hthird : (1 / 3 : ℝ) < 12 / 25 := by norm_num
      exact lt_trans hthird (lt_of_lt_of_le htopgt ha.1)
    have hratio : 1 - a < 2 * a := by linarith
    have hrough := roughDensity_eq_inv_of_lt_two a (1 - a) haPos hwNonneg hratio
    dsimp [H, G, F]
    rw [hrough]
    field_simp
  have hTailDenCont :
      ContinuousOn (fun a : ℝ => a * (1 - a)) (Set.Icc top (1 / 2 : ℝ)) := by
    fun_prop
  have hTailRatCont :
      ContinuousOn (fun a : ℝ => 1 / (a * (1 - a)))
        (Set.Icc top (1 / 2 : ℝ)) := by
    apply continuousOn_const.div hTailDenCont
    intro a ha
    have haPos : 0 < a := lt_of_lt_of_le htoppos ha.1
    have hwPos : 0 < 1 - a := by linarith [ha.2]
    exact ne_of_gt (mul_pos haPos hwPos)
  have hTailCont : ContinuousOn H (Set.Icc top (1 / 2 : ℝ)) :=
    hTailRatCont.congr (by
      intro a ha
      exact hTailEq a ha)
  have hTailInt : IntervalIntegrable H MeasureTheory.volume top (1 / 2 : ℝ) :=
    hTailCont.intervalIntegrable_of_Icc (le_of_lt htoplt)
  have hTopInt : IntervalIntegrable H MeasureTheory.volume b top := hBaseInt
  have hIntegralSplit :=
    intervalIntegral.integral_add_adjacent_intervals hTopInt hTailInt
  have hDensityIntegral := hp.identities.2.1 b hb (by
    have : b < κ := hbκ
    nlinarith [hκsmall])
  have hDensityIntegral' : (∫ a in b..(1 / 2 : ℝ), H a) = roughDensity b 1 - 1 := by
    simpa [H, G, F] using hDensityIntegral
  rw [← hIntegralSplit] at hDensityIntegral'
  have hTailNonneg : 0 ≤ ∫ a in top..(1 / 2 : ℝ), H a := by
    apply intervalIntegral.integral_nonneg (le_of_lt htoplt)
    intro a ha
    have haPos : 0 < a := lt_of_lt_of_le htoppos ha.1
    have hremPos : 0 < 1 - a := by linarith [ha.2]
    rw [hTailEq a ha]
    exact div_nonneg (by norm_num) (mul_nonneg haPos.le hremPos.le)
  have hIntegralBound : (∫ a in b..top, H a) ≤ roughDensity b 1 - 1 := by
    linarith [hDensityIntegral', hTailNonneg]
  have hPerBin (i : ℕ) (hi : i < N) :
      0 ≤ densityMeshSup b κ N i ∧
      (densityMeshSup b κ N i + η) *
          Real.log (densityMeshPoint b κ N (i + 1) / densityMeshPoint b κ N i) ≤
        (∫ a in densityMeshPoint b κ N i..
          densityMeshPoint b κ N (i + 1), H a) +
          2 * η * Real.log (densityMeshPoint b κ N (i + 1) /
            densityMeshPoint b κ N i) := by
    let left := densityMeshPoint b κ N i
    let right := densityMeshPoint b κ N (i + 1)
    let A := (fun a : ℝ => roughDensity left (1 - a)) '' Set.Icc left right
    have hiN : i + 1 ≤ N := by omega
    have hleftBounds := hPointBounds i (Nat.le_of_lt hi)
    have hrightBounds := hPointBounds (i + 1) hiN
    have hleftlt : left < right := by
      have hspan : 0 < right - left := by
        dsimp [left, right]
        rw [hStep]
        exact div_pos hwidth hNR
      exact sub_pos.mp hspan
    have hleftpos : 0 < left := lt_of_lt_of_le hb hleftBounds.1
    have hrightpos : 0 < right := lt_of_lt_of_le hb hrightBounds.1
    have hAne : A.Nonempty := by
      refine ⟨roughDensity left (1 - left), left, ?_, rfl⟩
      simp [left, right, le_of_lt hleftlt]
    have hpointBound (a a' : ℝ) (ha : a ∈ Set.Icc left right)
        (ha' : a' ∈ Set.Icc left right) :
        roughDensity left (1 - a') ≤ roughDensity a (1 - a) + η := by
      have hstep := hStep i
      have hdistla : dist left a' ≤ width / (N : ℝ) := by
        rw [Real.dist_eq]
        rw [abs_of_nonpos (sub_nonpos.mpr ha'.1)]
        have hspan : right - left = width / (N : ℝ) := by
          dsimp [left, right]
          exact hStep i
        linarith [hspan, ha'.2]
      have hdista : dist a' a ≤ width / (N : ℝ) := by
        rw [Real.dist_eq]
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2, ha'.1, ha'.2]
      have hleftK : (left, a') ∈ K := by
        simp only [K, Set.mem_prod, Set.mem_Icc]
        exact ⟨hleftBounds, ⟨le_trans hleftBounds.1 ha'.1, le_trans ha'.2 hrightBounds.2⟩⟩
      have hdiag'K : (a', a') ∈ K := by
        simp only [K, Set.mem_prod, Set.mem_Icc]
        exact ⟨⟨le_trans hleftBounds.1 ha'.1, le_trans ha'.2 hrightBounds.2⟩,
          ⟨le_trans hleftBounds.1 ha'.1, le_trans ha'.2 hrightBounds.2⟩⟩
      have hdiagK : (a, a) ∈ K := by
        simp only [K, Set.mem_prod, Set.mem_Icc]
        exact ⟨⟨le_trans hleftBounds.1 ha.1, le_trans ha.2 hrightBounds.2⟩,
          ⟨le_trans hleftBounds.1 ha.1, le_trans ha.2 hrightBounds.2⟩⟩
      have hdist1 : dist (left, a') (a', a') < δm := by
        rw [Prod.dist_eq]
        have hmax : max (dist left a') (dist a' a') ≤ width / (N : ℝ) := by
          exact max_le hdistla (by simpa using (div_pos hwidth hNR).le)
        exact lt_of_le_of_lt hmax hstepSmall
      have hdist2 : dist (a', a') (a, a) < δm := by
        rw [Prod.dist_eq]
        have hmax : max (dist a' a) (dist a' a) ≤ width / (N : ℝ) := by
          exact max_le hdista hdista
        exact lt_of_le_of_lt hmax hstepSmall
      have hnear1 := hclose (left, a') hleftK (a', a') hdiag'K hdist1
      have hnear2 := hclose (a', a') hdiag'K (a, a) hdiagK hdist2
      have hnear1' : |F (left, a') - F (a', a')| < η / 2 := by
        simpa [Real.dist_eq] using hnear1
      have hnear2' : |F (a', a') - F (a, a)| < η / 2 := by
        simpa [Real.dist_eq] using hnear2
      have hnear1'' :
          |roughDensity left (1 - a') - roughDensity a' (1 - a')| < η / 2 := by
        simpa [F] using hnear1'
      have hnear2'' :
          |roughDensity a' (1 - a') - roughDensity a (1 - a)| < η / 2 := by
        simpa [F] using hnear2'
      linarith [abs_lt.mp hnear1'', abs_lt.mp hnear2'']
    have hqUpper (a : ℝ) (ha : a ∈ Set.Icc left right) :
        sSup A ≤ roughDensity a (1 - a) + η := by
      apply csSup_le hAne
      intro y hy
      rcases hy with ⟨a', ha', rfl⟩
      exact hpointBound a a' ha ha'
    have hAbdd : BddAbove A := by
      refine ⟨roughDensity left (1 - left) + η, ?_⟩
      intro y hy
      rcases hy with ⟨a', ha', rfl⟩
      exact hpointBound left a' (by simp [left, right, le_of_lt hleftlt]) ha'
    have hSupNonneg : 0 ≤ sSup A := by
      have hdennonneg := roughDensity_nonneg left (1 - left) hleftpos (by linarith)
      have hmem : roughDensity left (1 - left) ∈ A :=
        ⟨left, by simp [left, right, le_of_lt hleftlt], rfl⟩
      have hle := le_csSup hAbdd hmem
      linarith
    have hq : sSup A = densityMeshSup b κ N i := by
      simp [A, left, right, densityMeshSup]
    have hqNonneg : 0 ≤ densityMeshSup b κ N i := by rw [← hq]; exact hSupNonneg
    have hqa (a : ℝ) (ha : a ∈ Set.Icc left right) :
        densityMeshSup b κ N i + η ≤ roughDensity a (1 - a) + 2 * η := by
      rw [← hq]
      linarith [hqUpper a ha]
    have hleftRight : left ≤ right := hleftlt.le
    have hbinHInt : IntervalIntegrable H MeasureTheory.volume left right := by
      have hsub : Set.Icc left right ⊆ Set.Icc b top := by
        intro a ha
        exact ⟨le_trans hleftBounds.1 ha.1, le_trans ha.2 hrightBounds.2⟩
      exact (hHcont.mono hsub).intervalIntegrable_of_Icc hleftRight
    have hbinEInt : IntervalIntegrable (fun a : ℝ => 1 / a) MeasureTheory.volume left right := by
      have hsub : Set.Icc left right ⊆ Set.Icc b top := by
        intro a ha
        exact ⟨le_trans hleftBounds.1 ha.1, le_trans ha.2 hrightBounds.2⟩
      exact (hEcont.mono hsub).intervalIntegrable_of_Icc hleftRight
    have hbinQInt : IntervalIntegrable (fun a : ℝ => (densityMeshSup b κ N i + η) / a)
        MeasureTheory.volume left right := by
      have hcont : ContinuousOn
          (fun a : ℝ => (densityMeshSup b κ N i + η) / a) (Set.Icc left right) := by
        apply continuousOn_const.div continuousOn_id
        intro a ha
        exact ne_of_gt (lt_of_lt_of_le hleftpos ha.1)
      exact hcont.intervalIntegrable_of_Icc hleftRight
    have hbinPairInt : IntervalIntegrable
        (fun a : ℝ => H a + 2 * η * (1 / a)) MeasureTheory.volume left right :=
      hbinHInt.add (hbinEInt.const_mul (2 * η))
    have hmono :
        (∫ a in left..right, (densityMeshSup b κ N i + η) / a) ≤
          ∫ a in left..right, H a + 2 * η * (1 / a) := by
      apply intervalIntegral.integral_mono_on hleftRight hbinQInt hbinPairInt
      intro a ha
      have hqa' := hqa a ha
      have haPos : 0 < a := lt_of_lt_of_le hleftpos ha.1
      have hnum := mul_le_mul_of_nonneg_right hqa' (le_of_lt haPos)
      have hpoint : (densityMeshSup b κ N i + η) / a ≤
          (roughDensity a (1 - a) + 2 * η) / a := by
        exact div_le_div_of_nonneg_right hqa' haPos.le
      simpa [H, G, F, div_eq_mul_inv, mul_add, add_mul, mul_assoc] using hpoint
    have hbinLog := integral_one_div_of_pos hleftpos hrightpos
    have hleftEq :
        (densityMeshSup b κ N i + η) * Real.log (right / left) =
          ∫ a in left..right, (densityMeshSup b κ N i + η) / a := by
      calc
        _ = (densityMeshSup b κ N i + η) * (∫ a in left..right, 1 / a) := by
          rw [hbinLog]
        _ = _ := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          funext a
          ring
    have hrightEq :
        (∫ a in left..right, H a + 2 * η * (1 / a)) =
          (∫ a in left..right, H a) +
            2 * η * Real.log (right / left) := by
      rw [intervalIntegral.integral_add hbinHInt (hbinEInt.const_mul (2 * η))]
      rw [intervalIntegral.integral_const_mul, hbinLog]
    refine ⟨hSupNonneg, ?_⟩
    dsimp [left, right] at hleftEq hrightEq ⊢
    linarith [hmono, hleftEq, hrightEq]
  have hsumBin :
      (∑ i ∈ Finset.range N,
        (densityMeshSup b κ N i + η) *
          Real.log (densityMeshPoint b κ N (i + 1) /
            densityMeshPoint b κ N i)) ≤
        (∫ a in b..top, H a) + 2 * η * logRange := by
    calc
      _ ≤ ∑ i ∈ Finset.range N,
          ((∫ a in densityMeshPoint b κ N i..
              densityMeshPoint b κ N (i + 1), H a) +
            2 * η * Real.log (densityMeshPoint b κ N (i + 1) /
              densityMeshPoint b κ N i)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact (hPerBin i (Finset.mem_range.mp hi)).2
      _ = (∫ a in b..top, H a) + 2 * η * logRange := by
            rw [Finset.sum_add_distrib, hsumH, ← Finset.mul_sum, hlogsum]
  have hErr : 2 * η * logRange ≤ ε := by
    dsimp [η]
    have hden : 0 < 2 * (logRange + 1) := by positivity
    have hfrac : logRange / (logRange + 1) ≤ 1 := by
      rw [div_le_one (by linarith : 0 < logRange + 1)]
      linarith
    calc
      2 * (ε / (2 * (logRange + 1))) * logRange =
          ε * (logRange / (logRange + 1)) := by
            field_simp [ne_of_gt hden]
            <;> ring
      _ ≤ ε := by nlinarith [mul_le_mul_of_nonneg_left hfrac hε.le]
  refine ⟨N, hN, ?_, ?_⟩
  · intro i hi
    exact (hPerBin i hi).1
  · calc
      _ = (∑ i ∈ Finset.range N,
          (densityMeshSup b κ N i + η) *
            Real.log (densityMeshPoint b κ N (i + 1) /
              densityMeshPoint b κ N i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ ≤ (∫ a in b..top, H a) + 2 * η * logRange := hsumBin
      _ ≤ roughDensity b 1 - 1 + ε := by
        linarith [hIntegralBound, hErr]

/-- A nonzero Type II error box contains a supported factor pair. -/
theorem roughProxyErrorBox_exists_supported_pair
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (γ γ' S : ℝ) (U V : ℕ)
    (hBox : roughProxyErrorBox C.bands x jstar C.psi γ γ' S U V ≠ 0) :
    ∃ m ∈ Finset.Ico U (2 * U), ∃ p ∈ Finset.Ico V (2 * V),
      Odd (m * p) ∧ 1 < m * p ∧
      (Nat.Prime p ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ') ∧
      C.weighted x jstar ((m * p - 1) / 2) ≠ 0 := by
  classical
  unfold roughProxyErrorBox at hBox
  have hexists :
      ∃ m ∈ Finset.Ico U (2 * U), ∃ p ∈ Finset.Ico V (2 * V),
        (if Odd (m * p) ∧ 1 < m * p then
          C.bands.weight x jstar ((m * p - 1) / 2) *
            C.psi (((m * p - 1 : ℕ) / 2 : ℕ) / x) *
              (test (.rough γ) x m - proxy (.rough γ) x S m) *
                (if p.Prime ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' then 1 else 0)
         else 0) ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hBox
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro p hp
    exact hnone m hm p hp
  obtain ⟨m, hm, p, hp, hterm⟩ := hexists
  have hodd : Odd (m * p) ∧ 1 < m * p := by
    by_contra hbad
    simp [hbad] at hterm
  have hbin : Nat.Prime p ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' := by
    by_contra hbad
    simp [hodd, hbad] at hterm
  let u : ℕ := (m * p - 1) / 2
  have hweighted : C.weighted x jstar u ≠ 0 := by
    have hterm' : C.weighted x jstar u *
        (test (.rough γ) x m - proxy (.rough γ) x S m) ≠ 0 := by
      simpa [u, CandidateData.weighted, hodd, hbin] using hterm
    intro hzero
    simp [hzero] at hterm'
  have hprod : m * p = 2 * u + 1 := by
    rcases hodd.1 with ⟨k, hk⟩
    have hu : u = k := by
      dsimp [u]
      rw [hk]
      omega
    rw [hu]
    exact hk
  exact ⟨m, hm, p, hp, hodd.1, hodd.2, hbin, by simpa [u] using hweighted⟩

/-- A supported pair in an unbalanced-bin error box satisfies every Type II
dyadic factor and product range. -/
theorem roughProxyErrorBox_ranges
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (γ γ' S : ℝ) (U V : ℕ)
    (b bstar κ : ℝ) (hx : 3 ≤ x) (hb : 0 < b) (hbstar : 0 < bstar)
    (hbstarSmall : bstar < 1 / 2) (hbstarEq : b = 3 * bstar)
    (hSlack : 5 ≤ x ^ (2 * bstar)) (hκ : 0 < κ)
    (hγ : b ≤ γ) (hγlt : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ)
    (hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hBox : roughProxyErrorBox C.bands x jstar C.psi γ γ' S U V ≠ 0) :
    x / 8 ≤ (U : ℝ) * (V : ℝ) ∧
      (U : ℝ) * (V : ℝ) ≤ 8 * x ∧
      x ^ bstar ≤ (U : ℝ) ∧ (U : ℝ) ≤ x ^ (1 - bstar) ∧
      x ^ bstar ≤ (V : ℝ) ∧ (V : ℝ) ≤ x ^ (1 - bstar) := by
  obtain ⟨m, hm, p, hpMem, hodd, hmulGt, hbin, hweight⟩ :=
    roughProxyErrorBox_exists_supported_pair C x jstar γ γ' S U V hBox
  let u : ℕ := (m * p - 1) / 2
  rcases hodd with ⟨k, hk⟩
  have hu : u = k := by
    dsimp [u]
    rw [hk]
    omega
  have hprod : m * p = 2 * u + 1 := by
    rw [hu]
    exact hk
  have hsup := hSupport u hweight
  exact pair_box_ranges_core x b bstar κ γ γ' m p u U V hx hb hbstar
    hbstarSmall hbstarEq hSlack hγ (by linarith [hγ']) hκ
    hm hpMem hprod hsup hbin.1 hbin.2.1 hbin.2.2

/-- Type II controls every box in an unbalanced exponent bin: boxes outside
its admissible ranges vanish by the candidate support conditions. -/
theorem typeII_unbalanced_box_bound
    (hII : TypeIIEstimate) (hp : ProxyInputs) (C : CandidateData) (δ : ℝ)
    (hBounds : C.Bounds δ) (hValid : C.bands.Valid)
    (hPsi : ContDiff ℝ ∞ C.psi)
    (hPsiSupport : Function.support C.psi ⊆ Set.Icc 1 2)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (Dsave bstar b κ γ γ' : ℝ)
    (hDsave : 0 < Dsave) (hbstar : 0 < bstar)
    (hbstarSmall : bstar < 1 / 2) (hbstarEq : b = 3 * bstar)
    (hslot : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hγ : b ≤ γ) (hγlt : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ S : ℝ, 2 * B + 3 < S → ∀ᶠ x : ℝ in atTop,
        ∀ U V : ℕ,
          |roughProxyErrorBox C.bands x jstar C.psi γ γ' S U V| ≤
            K * x * Analytic.L x ^ (-Dsave) := by
  obtain ⟨B, K, hB, hK, hError⟩ :=
    typeII_roughProxyErrorBox_bound hII hp C hValid hPsi hPsiSupport jstar
      Dsave bstar b κ γ γ' hDsave hbstar hslot hb hκ hκsmall hγ hγlt hγ'
  obtain ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩ := hBounds
  have hCandidateEvent := hBound jstar hjstar
  have hXEvent : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  have hSlackEvent : ∀ᶠ x : ℝ in atTop, 5 ≤ x ^ (2 * bstar) := by
    have hexp : 0 < 2 * bstar := by positivity
    exact (tendsto_rpow_atTop hexp).eventually_ge_atTop 5
  have hProxyAmbientEvent : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (bstar / 4) := by
    have hexp : 0 < bstar / 4 := by positivity
    exact (tendsto_rpow_atTop hexp).eventually_ge_atTop 2
  refine ⟨B, K, hB, hK, ?_⟩
  intro S hS
  filter_upwards [hError S hS, hCandidateEvent, hXEvent,
    hSlackEvent, hProxyAmbientEvent] with x hIIData hCandidate hx hSlack hAmbient
  rcases hIIData with ⟨hxgt, hL, hW, hBoxBound⟩
  rcases hCandidate with ⟨_, _, _, _, _, hCandidateSupport⟩
  have hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x := by
    intro u hu
    rcases hCandidateSupport u hu with ⟨hlo, hhi, _⟩
    exact ⟨hlo, hhi⟩
  intro U V
  by_cases hZero : roughProxyErrorBox C.bands x jstar C.psi γ γ' S U V = 0
  · simp [hZero]
    positivity
  · have hRanges := roughProxyErrorBox_ranges C x jstar γ γ' S U V
      b bstar κ hx hb hbstar hbstarSmall hbstarEq hSlack hκ hγ hγlt hγ'
      hSupport hZero
    rcases hRanges with ⟨hProdLo, hProdHi, hULo, hUHi, hVLo, hVHi⟩
    have hxone : 1 ≤ x := le_trans (by norm_num : (1 : ℝ) ≤ 3) hx
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hxone
    have hExpoLo : b / 4 ≤ bstar := by rw [hbstarEq]; nlinarith
    have hUambientLo : x ^ (b / 4) ≤ (U : ℝ) :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hxone hExpoLo) hULo
    have hExpoHi : 1 - bstar ≤ 1 - b / 4 := by rw [hbstarEq]; nlinarith
    have hUambientHi : (U : ℝ) ≤ x ^ (1 - b / 4) :=
      le_trans hUHi (Real.rpow_le_rpow_of_exponent_le hxone hExpoHi)
    have hPowerMul :
        x ^ (1 - bstar) * x ^ (bstar / 4) = x ^ (1 - b / 4) := by
      rw [← Real.rpow_add hxpos, hbstarEq]
      congr 1
      ring
    have h2U : 2 * (U : ℝ) ≤ x ^ (1 - b / 4) := by
      calc
        2 * (U : ℝ) ≤ 2 * x ^ (1 - bstar) :=
          mul_le_mul_of_nonneg_left hUHi (by norm_num)
        _ = x ^ (1 - bstar) * 2 := by ring
        _ ≤ x ^ (1 - bstar) * x ^ (bstar / 4) :=
          mul_le_mul_of_nonneg_left hAmbient
            (Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hxone) _)
        _ = x ^ (1 - b / 4) := hPowerMul
    have hNatHi : ((2 * U - 1 : ℕ) : ℝ) ≤ x ^ (1 - b / 4) := by
      have hnat : 2 * U - 1 ≤ 2 * U := Nat.sub_le _ _
      calc
        ((2 * U - 1 : ℕ) : ℝ) ≤ ((2 * U : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = 2 * (U : ℝ) := by norm_num
        _ ≤ x ^ (1 - b / 4) := h2U
    exact hBoxBound U V hProdLo hProdHi hULo hUHi hVLo hVHi
      hUambientLo hNatHi

def roughProxyErrorTerm (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (γ γ' S : ℝ) (m p : ℕ) : ℝ :=
  if Odd (m * p) ∧ 1 < m * p then
    C.weighted x jstar ((m * p - 1) / 2) *
      (test (.rough γ) x m - proxy (.rough γ) x S m) *
        (if p.Prime ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' then 1 else 0)
  else 0

def roughProxyErrorPairSum (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (γ γ' S : ℝ) (K : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 (2 ^ K),
    ∑ p ∈ Finset.Ico 1 (2 ^ K), roughProxyErrorTerm C x jstar γ γ' S m p

/-- Reindex the finite factor-pair error sum by its complete family of
natural dyadic boxes. -/
theorem roughProxyErrorPairSum_eq_boxes
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (γ γ' S : ℝ) (K : ℕ) :
    roughProxyErrorPairSum C x jstar γ γ' S K =
      ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
        roughProxyErrorBox C.bands x jstar C.psi γ γ' S (2 ^ k) (2 ^ l) := by
  classical
  unfold roughProxyErrorPairSum
  rw [sum_nat_pair_dyadic_boxes K (roughProxyErrorTerm C x jstar γ γ' S)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  simp [roughProxyErrorBox, roughProxyErrorTerm, CandidateData.weighted,
    Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem mem_primesUpTo_iff (y : ℝ) (hy : 0 ≤ y) (p : ℕ) :
    p ∈ primesUpTo y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  rw [Nat.le_floor_iff hy]
  constructor
  · rintro ⟨⟨_, hpY⟩, hp⟩
    exact ⟨hp, hpY⟩
  · rintro ⟨hp, hpY⟩
    exact ⟨⟨hp.one_le, hpY⟩, hp⟩

theorem candidate_weighted_support_mem (C : CandidateData) (x : ℝ) (jstar u : ℕ)
    (hx : 3 ≤ x)
    (hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hweight : C.weighted x jstar u ≠ 0) :
    u ∈ Finset.Icc 1 ⌊2 * x⌋₊ := by
  have hsup := hSupport u hweight
  have huone : 1 ≤ u := by
    have hxone : (1 : ℝ) ≤ x := by linarith
    have : (1 : ℝ) ≤ (u : ℝ) := le_trans hxone hsup.1
    exact_mod_cast this
  have hufloor : u ≤ ⌊2 * x⌋₊ :=
    (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 2 * x)).2 hsup.2
  exact Finset.mem_Icc.mpr ⟨huone, hufloor⟩

/-- Reindex odd factor pairs by their shifted integer and the selected
divisor. The image form keeps only divisor pairs represented in the chosen
factor rectangle. -/
theorem sum_factor_pair_to_image
    (M U P : Finset ℕ) (hPpos : ∀ p ∈ P, 0 < p) (g : ℕ → ℕ → ℝ) :
    let S := (M ×ˢ P).filter (fun z =>
      Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 ∧ ((z.1 * z.2 - 1) / 2) ∈ U)
    let φ : ℕ × ℕ → ℕ × ℕ := fun z => ((z.1 * z.2 - 1) / 2, z.2)
    (∑ z ∈ S, g z.1 z.2) =
      ∑ z ∈ S.image φ, g ((2 * z.1 + 1) / z.2) z.2 := by
  classical
  dsimp
  let S := (M ×ˢ P).filter (fun z =>
    Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 ∧ ((z.1 * z.2 - 1) / 2) ∈ U)
  let φ : ℕ × ℕ → ℕ × ℕ := fun z => ((z.1 * z.2 - 1) / 2, z.2)
  refine Finset.sum_bij (fun z _ => φ z) ?_ ?_ ?_ ?_
  · intro z hz
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  · intro z₁ hz₁ z₂ hz₂ hEq
    rcases z₁ with ⟨m₁, p₁⟩
    rcases z₂ with ⟨m₂, p₂⟩
    have hp₁mem : p₁ ∈ P := (Finset.mem_product.mp
      (Finset.mem_filter.mp hz₁).1).2
    have hp₂mem : p₂ ∈ P := (Finset.mem_product.mp
      (Finset.mem_filter.mp hz₂).1).2
    have huEq : (m₁ * p₁ - 1) / 2 = (m₂ * p₂ - 1) / 2 := congrArg Prod.fst hEq
    have hpEq : p₁ = p₂ := congrArg Prod.snd hEq
    subst p₂
    have hodd₁ := (Finset.mem_filter.mp hz₁).2.1
    have hodd₂ := (Finset.mem_filter.mp hz₂).2.1
    rcases hodd₁ with ⟨k₁, hk₁⟩
    rcases hodd₂ with ⟨k₂, hk₂⟩
    have hk₁' : (m₁ * p₁ - 1) / 2 = k₁ := by rw [hk₁]; omega
    have hk₂' : (m₂ * p₁ - 1) / 2 = k₂ := by rw [hk₂]; omega
    have hmul₁ : m₁ * p₁ = 2 * ((m₁ * p₁ - 1) / 2) + 1 := by rw [hk₁', hk₁]
    have hmul₂ : m₂ * p₁ = 2 * ((m₂ * p₁ - 1) / 2) + 1 := by rw [hk₂', hk₂]
    have hmulEq : m₁ * p₁ = m₂ * p₁ := by
      calc
        m₁ * p₁ = 2 * ((m₁ * p₁ - 1) / 2) + 1 := hmul₁
        _ = 2 * ((m₂ * p₁ - 1) / 2) + 1 := by rw [huEq]
        _ = m₂ * p₁ := hmul₂.symm
    have hpPos := hPpos p₁ hp₁mem
    have hmEq : m₁ = m₂ := Nat.mul_right_cancel hpPos hmulEq
    subst m₂
    rfl
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨z, hzS, rfl⟩
    exact ⟨z, hzS, rfl⟩
  · intro z hz
    rcases z with ⟨m, p⟩
    have hz' := (Finset.mem_filter.mp hz).2
    rcases hz' with ⟨hodd, hgt, huU⟩
    have hpMem : p ∈ P := (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2
    rcases hodd with ⟨k, hk⟩
    have hu : (m * p - 1) / 2 = k := by rw [hk]; omega
    have hprod : m * p = 2 * ((m * p - 1) / 2) + 1 := by rw [hu, hk]
    have hdiv : p ∣ 2 * ((m * p - 1) / 2) + 1 := by
      rw [← hprod]
      exact ⟨m, by rw [Nat.mul_comm]⟩
    have hq : (2 * ((m * p - 1) / 2) + 1) / p = m := by
      apply Nat.mul_right_cancel (hPpos p hpMem)
      calc
        ((2 * ((m * p - 1) / 2) + 1) / p) * p =
            2 * ((m * p - 1) / 2) + 1 := Nat.div_mul_cancel hdiv
        _ = m * p := hprod.symm
    have hmpDiv : (m * p) / p = m := by
      rw [hprod]
      exact hq
    change g m p = g (((2 * ((m * p - 1) / 2) + 1) / p)) p
    rw [← hprod]
    exact congrArg (fun q => g q p) hmpDiv.symm

/-- Restrict the Type II pair error to candidate support and reindex it as a
finite divisor-pair sum. -/
theorem roughProxyErrorPairSum_eq_supported_divisor_image
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (γ γ' S : ℝ) (K : ℕ)
    (hx : 3 ≤ x)
    (hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x) :
    let M := Finset.Ico 1 (2 ^ K)
    let U := Finset.Icc 1 ⌊2 * x⌋₊
    let isBin := fun p : ℕ => Nat.Prime p ∧
      x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
    let P := M.filter isBin
    let Src := (M ×ˢ P).filter (fun z => Odd (z.1 * z.2) ∧
      1 < z.1 * z.2 ∧ ((z.1 * z.2 - 1) / 2) ∈ U)
    let φ : ℕ × ℕ → ℕ × ℕ := fun z => ((z.1 * z.2 - 1) / 2, z.2)
    roughProxyErrorPairSum C x jstar γ γ' S K =
      ∑ z ∈ Src.image φ,
        C.weighted x jstar (((((2 * z.1 + 1) / z.2) * z.2 - 1) / 2)) *
          (test (.rough γ) x ((2 * z.1 + 1) / z.2) -
            proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) := by
  classical
  dsimp
  let M := Finset.Ico 1 (2 ^ K)
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let isBin := fun p : ℕ => Nat.Prime p ∧
    x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
  let P := M.filter isBin
  let Sset := (M ×ˢ P).filter (fun z => Odd (z.1 * z.2) ∧
    1 < z.1 * z.2 ∧ ((z.1 * z.2 - 1) / 2) ∈ U)
  let φ : ℕ × ℕ → ℕ × ℕ := fun z => ((z.1 * z.2 - 1) / 2, z.2)
  let g : ℕ → ℕ → ℝ := fun m p =>
    C.weighted x jstar ((m * p - 1) / 2) *
      (test (.rough γ) x m - proxy (.rough γ) x S m)
  have hPpos : ∀ p ∈ P, 0 < p := by
    intro p hp
    have hpM := (Finset.mem_filter.mp hp).1
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Ico.mp hpM).1
  have hPairP : roughProxyErrorPairSum C x jstar γ γ' S K =
      ∑ m ∈ M, ∑ p ∈ P,
        if Odd (m * p) ∧ 1 < m * p then g m p else 0 := by
    unfold roughProxyErrorPairSum
    have hEach (m : ℕ) (hm : m ∈ M) :
        (∑ p ∈ M, roughProxyErrorTerm C x jstar γ γ' S m p) =
          ∑ p ∈ P, if Odd (m * p) ∧ 1 < m * p then g m p else 0 := by
      have hterm (p : ℕ) (hp : p ∈ M) :
          roughProxyErrorTerm C x jstar γ γ' S m p =
            if p ∈ P then
              (if Odd (m * p) ∧ 1 < m * p then g m p else 0)
            else 0 := by
        by_cases hbin : isBin p
        · have hpP : p ∈ P := Finset.mem_filter.mpr ⟨hp, hbin⟩
          simp [roughProxyErrorTerm, hbin, hpP, g, isBin]
        · have hpP : p ∉ P := by simp [P, hbin]
          simp [roughProxyErrorTerm, hbin, hpP, isBin]
      calc
        _ = ∑ p ∈ M, if p ∈ P then
              (if Odd (m * p) ∧ 1 < m * p then g m p else 0) else 0 := by
                apply Finset.sum_congr rfl
                intro p hp
                exact hterm p hp
        _ = ∑ p ∈ M.filter (fun p => p ∈ P),
              (if Odd (m * p) ∧ 1 < m * p then g m p else 0) := by
                rw [Finset.sum_filter]
        _ = ∑ p ∈ P, if Odd (m * p) ∧ 1 < m * p then g m p else 0 := by
                have hfilter : M.filter (fun p => p ∈ P) = P := by
                  ext p
                  simp only [Finset.mem_filter]
                  constructor
                  · exact fun h => h.2
                  · intro hp
                    exact ⟨(Finset.mem_filter.mp hp).1, hp⟩
                rw [hfilter]
    apply Finset.sum_congr rfl
    intro m hm
    exact hEach m hm
  have hsumProduct :
      (∑ m ∈ M, ∑ p ∈ P,
        if Odd (m * p) ∧ 1 < m * p then g m p else 0) =
        ∑ z ∈ M ×ˢ P, if Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 then
          g z.1 z.2 else 0 := by
    simpa using (Finset.sum_product' M P
      (fun m p => if Odd (m * p) ∧ 1 < m * p then g m p else 0)).symm
  have hrestricted :
      (∑ z ∈ M ×ˢ P, if Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 then
        g z.1 z.2 else 0) = ∑ z ∈ Sset, g z.1 z.2 := by
    calc
      _ = ∑ z ∈ M ×ˢ P,
          if Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 ∧
            ((z.1 * z.2 - 1) / 2) ∈ U then g z.1 z.2 else 0 := by
              apply Finset.sum_congr rfl
              intro z hz
              by_cases hodd : Odd (z.1 * z.2)
              · by_cases hgt : 1 < z.1 * z.2
                · by_cases hu : ((z.1 * z.2 - 1) / 2) ∈ U
                  · simp [hodd, hgt, hu]
                  · have hweightZero :
                      C.weighted x jstar ((z.1 * z.2 - 1) / 2) = 0 := by
                      by_contra hne
                      exact hu (candidate_weighted_support_mem C x jstar
                        ((z.1 * z.2 - 1) / 2) hx hSupport hne)
                    simp [hodd, hgt, hu, g, hweightZero]
                · simp [hodd, hgt]
              · simp [hodd]
      _ = ∑ z ∈ Sset, g z.1 z.2 := by
            rw [Finset.sum_filter]
  have hImage := sum_factor_pair_to_image M U P hPpos g
  calc
    roughProxyErrorPairSum C x jstar γ γ' S K =
        ∑ z ∈ Sset, g z.1 z.2 := by rw [hPairP, hsumProduct, hrestricted]
    _ = ∑ z ∈ Sset.image φ, g ((2 * z.1 + 1) / z.2) z.2 := by
      simpa [Sset, φ, g] using hImage

/-- With a cutoff above the candidate product range, the supported factor
image is the full set of prime-bin divisor pairs. -/
theorem candidate_bin_divisor_image_eq
    (x γ γ' : ℝ) (K : ℕ) (hx : 3 ≤ x)
    (hCut : 5 * x < ((2 ^ K : ℕ) : ℝ)) :
    let M := Finset.Ico 1 (2 ^ K)
    let U := Finset.Icc 1 ⌊2 * x⌋₊
    let P := M.filter (fun p => Nat.Prime p ∧
      x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ')
    let S := (M ×ˢ P).filter (fun z => Odd (z.1 * z.2) ∧
      1 < z.1 * z.2 ∧ ((z.1 * z.2 - 1) / 2) ∈ U)
    let φ : ℕ × ℕ → ℕ × ℕ := fun z => ((z.1 * z.2 - 1) / 2, z.2)
    S.image φ = (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1) := by
  classical
  dsimp
  let M := Finset.Ico 1 (2 ^ K)
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let P := M.filter (fun p => Nat.Prime p ∧
    x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ')
  let S := (M ×ˢ P).filter (fun z => Odd (z.1 * z.2) ∧
    1 < z.1 * z.2 ∧ ((z.1 * z.2 - 1) / 2) ∈ U)
  let φ : ℕ × ℕ → ℕ × ℕ := fun z => ((z.1 * z.2 - 1) / 2, z.2)
  let T := (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1)
  apply Finset.Subset.antisymm
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨⟨m, p⟩, hsrc, rfl⟩
    rcases (Finset.mem_filter.mp hsrc).2 with ⟨hodd, hgt, huU⟩
    have hpP : p ∈ P := (Finset.mem_product.mp (Finset.mem_filter.mp hsrc).1).2
    rcases hodd with ⟨k, hk⟩
    have hu : (m * p - 1) / 2 = k := by rw [hk]; omega
    have hprod : m * p = 2 * ((m * p - 1) / 2) + 1 := by rw [hu, hk]
    have hdiv : p ∣ 2 * ((m * p - 1) / 2) + 1 := by
      rw [← hprod]
      exact ⟨m, by rw [Nat.mul_comm]⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨huU, hpP⟩, hdiv⟩
  · intro z hz
    rcases z with ⟨u, p⟩
    rcases Finset.mem_filter.mp hz with ⟨hUP, hdiv⟩
    rcases Finset.mem_product.mp hUP with ⟨huU, hpP⟩
    have hpPos : 0 < p := by
      have hpM := (Finset.mem_filter.mp hpP).1
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Ico.mp hpM).1
    have hNpos : 0 < 2 * u + 1 := by
      have huLo := (Finset.mem_Icc.mp huU).1
      omega
    let m : ℕ := (2 * u + 1) / p
    have hprod : m * p = 2 * u + 1 := by
      exact Nat.div_mul_cancel hdiv
    have hmPos : 0 < m := by
      have hpLe : p ≤ 2 * u + 1 := Nat.le_of_dvd hNpos hdiv
      dsimp [m]
      exact Nat.div_pos hpLe hpPos
    have huReal : (u : ℝ) ≤ 2 * x := by
      have huFloor := (Finset.mem_Icc.mp huU).2
      exact le_trans (Nat.cast_le.mpr huFloor) (Nat.floor_le (by positivity))
    have hNreal : ((2 * u + 1 : ℕ) : ℝ) ≤ 5 * x := by
      have hx1 : (1 : ℝ) ≤ x := by linarith
      push_cast
      nlinarith [huReal, hx1]
    have hNlt : 2 * u + 1 < 2 ^ K := by
      exact_mod_cast lt_of_le_of_lt hNreal hCut
    have hmLt : m < 2 ^ K := lt_of_le_of_lt (Nat.div_le_self _ _) hNlt
    have hmM : m ∈ M := by
      simp [M, Finset.mem_Ico, Nat.one_le_iff_ne_zero.mpr hmPos.ne']
      exact hmLt
    have hodd : Odd (m * p) := ⟨u, hprod⟩
    have hgt : 1 < m * p := by
      have huLo := (Finset.mem_Icc.mp huU).1
      rw [hprod]
      omega
    have hquot : (m * p - 1) / 2 = u := by rw [hprod]; omega
    have hsrc : (m, p) ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hmM, hpP⟩, hodd, hgt, ?_⟩
      change (m * p - 1) / 2 ∈ Finset.Icc 1 ⌊2 * x⌋₊
      rw [hquot]
      exact huU
    have hφ : φ (m, p) = (u, p) := by simp [φ, hquot]
    exact Finset.mem_image.mpr ⟨(m, p), hsrc, hφ⟩

/-- The factor-pair error is the divisor-pair error with the shifted
candidate weight simplified back to its original index. -/
theorem roughProxyErrorPairSum_eq_divisorSum
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (γ γ' S : ℝ) (K : ℕ)
    (hx : 3 ≤ x) (hCut : 5 * x < ((2 ^ K : ℕ) : ℝ))
    (hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x) :
    let M := Finset.Ico 1 (2 ^ K)
    let U := Finset.Icc 1 ⌊2 * x⌋₊
    let isBin := fun p : ℕ => Nat.Prime p ∧
      x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
    let P := M.filter isBin
    roughProxyErrorPairSum C x jstar γ γ' S K =
      ∑ z ∈ (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1),
        C.weighted x jstar z.1 *
          (test (.rough γ) x ((2 * z.1 + 1) / z.2) -
            proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) := by
  classical
  dsimp
  let M := Finset.Ico 1 (2 ^ K)
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let isBin := fun p : ℕ => Nat.Prime p ∧
    x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
  let P := M.filter isBin
  let Src := (M ×ˢ P).filter (fun z => Odd (z.1 * z.2) ∧
    1 < z.1 * z.2 ∧ ((z.1 * z.2 - 1) / 2) ∈ U)
  let φ : ℕ × ℕ → ℕ × ℕ := fun z => ((z.1 * z.2 - 1) / 2, z.2)
  let T := (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1)
  have hPair := roughProxyErrorPairSum_eq_supported_divisor_image
    C x jstar γ γ' S K hx hSupport
  have hImage : Src.image φ = T := by
    simpa [Src, T, M, U, P, isBin, φ] using
      candidate_bin_divisor_image_eq x γ γ' K hx hCut
  rw [hPair, hImage]
  apply Finset.sum_congr rfl
  intro z hz
  rcases z with ⟨u, p⟩
  have hdiv : p ∣ 2 * u + 1 := (Finset.mem_filter.mp hz).2
  have hmul : ((2 * u + 1) / p) * p = 2 * u + 1 :=
    Nat.div_mul_cancel hdiv
  have hquot : (((2 * u + 1) / p) * p - 1) / 2 = u := by
    rw [hmul]
    omega
  rw [hquot]

/-- Split the reindexed Type II error into its actual rough-factor mass minus
the proxy mass. -/
theorem roughProxyErrorPairSum_eq_actual_sub_proxy
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (γ γ' S : ℝ) (K : ℕ)
    (hx : 3 ≤ x) (hCut : 5 * x < ((2 ^ K : ℕ) : ℝ))
    (hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x) :
    let M := Finset.Ico 1 (2 ^ K)
    let U := Finset.Icc 1 ⌊2 * x⌋₊
    let isBin := fun p : ℕ => Nat.Prime p ∧
      x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
    let P := M.filter isBin
    let T := (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1)
    roughProxyErrorPairSum C x jstar γ γ' S K =
      (∑ z ∈ T, C.weighted x jstar z.1 *
        test (.rough γ) x ((2 * z.1 + 1) / z.2)) -
      ∑ z ∈ T, C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2) := by
  classical
  dsimp
  let M := Finset.Ico 1 (2 ^ K)
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let isBin := fun p : ℕ => Nat.Prime p ∧
    x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
  let P := M.filter isBin
  let T := (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1)
  have hDiv := roughProxyErrorPairSum_eq_divisorSum C x jstar γ γ' S K
    hx hCut hSupport
  have hDiv' := by simpa [M, U, isBin, P, T] using hDiv
  calc
    roughProxyErrorPairSum C x jstar γ γ' S K =
        ∑ z ∈ T, C.weighted x jstar z.1 *
          (test (.rough γ) x ((2 * z.1 + 1) / z.2) -
            proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) := hDiv'
    _ = ∑ z ∈ T, (C.weighted x jstar z.1 *
          test (.rough γ) x ((2 * z.1 + 1) / z.2) -
        C.weighted x jstar z.1 *
          proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) := by
          apply Finset.sum_congr rfl
          intro z hz
          ring
    _ = _ := by rw [Finset.sum_sub_distrib]

/-- The proxy part of a prime-bin divisor sum is exactly the fixed-prime
survivor proxy sum at the auxiliary roughness cutoff `W`. -/
theorem roughProxyDivisorProxySum_eq_fixedPrime
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (γ γ' S : ℝ)
    (P : Finset ℕ)
    (hPPrime : ∀ p ∈ P, Nat.Prime p)
    (hPBin : ∀ p ∈ P, x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ')
    (hW : 1 ≤ Analytic.W x) (hWγ : Analytic.W x ≤ x ^ γ) :
    let U := Finset.Icc 1 ⌊2 * x⌋₊
    let T := (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1)
    (∑ z ∈ T, C.weighted x jstar z.1 *
      proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) =
      ∑ p ∈ P, primeDivisorProxySiftedMass C x jstar p
        (Analytic.W x) γ S := by
  classical
  dsimp
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let T := (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1)
  let f := fun u p => C.weighted x jstar u *
    proxy (.rough γ) x S ((2 * u + 1) / p)
  have hPair : (∑ z ∈ T, f z.1 z.2) =
      ∑ p ∈ P, ∑ u ∈ U, if p ∣ 2 * u + 1 then f u p else 0 := by
    calc
      _ = ∑ z ∈ U ×ˢ P,
          if z.2 ∣ 2 * z.1 + 1 then f z.1 z.2 else 0 := by
            rw [← Finset.sum_filter]
      _ = ∑ u ∈ U, ∑ p ∈ P,
          if p ∣ 2 * u + 1 then f u p else 0 := by
            simpa [f] using (Finset.sum_product' U P
              (fun u p => if p ∣ 2 * u + 1 then
                C.weighted x jstar u *
                  proxy (.rough γ) x S ((2 * u + 1) / p) else 0))
      _ = ∑ p ∈ P, ∑ u ∈ U,
          if p ∣ 2 * u + 1 then f u p else 0 := by
            rw [Finset.sum_comm]
  have hterm (u p : ℕ) (hpP : p ∈ P) :
      (if p ∣ 2 * u + 1 then f u p else 0) =
        if (p ∣ 2 * u + 1 ∧
            (∀ q ∈ (primesUpTo (Analytic.W x)).erase 2,
              ¬ q ∣ 2 * u + 1)) ∧ C.weighted x jstar u ≠ 0 then
          C.weighted x jstar u *
            proxy (.rough γ) x S ((2 * u + 1) / p) else 0 := by
    by_cases hdiv : p ∣ 2 * u + 1
    · have hpPrime : Nat.Prime p := hPPrime p hpP
      have hpLo : x ^ γ < (p : ℝ) := (hPBin p hpP).1
      have hpW : Analytic.W x < (p : ℝ) := lt_of_le_of_lt hWγ hpLo
      have hOdd : Odd (2 * u + 1) := by simp
      have hroughIff := rough_iff_survives_odd_prime_sieve
        (Analytic.W x) (2 * u + 1) hW hOdd
      have hmul : ((2 * u + 1) / p) * p = 2 * u + 1 :=
        Nat.div_mul_cancel hdiv
      by_cases hSurv : ∀ q ∈ (primesUpTo (Analytic.W x)).erase 2,
          ¬ q ∣ 2 * u + 1
      · by_cases hw : C.weighted x jstar u = 0
        · simp [hdiv, hw, f]
        · have hCond : (p ∣ 2 * u + 1 ∧
              (∀ q ∈ (primesUpTo (Analytic.W x)).erase 2,
                ¬ q ∣ 2 * u + 1)) ∧ C.weighted x jstar u ≠ 0 :=
            ⟨⟨hdiv, hSurv⟩, hw⟩
          simp only [if_pos hdiv, if_pos hCond, f]
      · have hnotN : ¬ Analytic.rough (Analytic.W x) (2 * u + 1) :=
          fun hN => hSurv (hroughIff.1 hN)
        have hroughP : Analytic.rough (Analytic.W x) p := by
          refine ⟨hpPrime.pos, ?_⟩
          intro q hq hqdvd
          have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hpPrime).mp hqdvd
          subst q
          exact hpW
        have hnotCof : ¬ Analytic.rough (Analytic.W x) ((2 * u + 1) / p) := by
          intro hCof
          have hroughProd := rough_mul hCof hroughP
          rw [hmul] at hroughProd
          exact hnotN hroughProd
        have hproxy : proxy (.rough γ) x S ((2 * u + 1) / p) = 0 := by
          simp [proxy, hnotCof]
        have hCond : ¬ ((p ∣ 2 * u + 1 ∧
            (∀ q ∈ (primesUpTo (Analytic.W x)).erase 2,
              ¬ q ∣ 2 * u + 1)) ∧ C.weighted x jstar u ≠ 0) := by
          intro hh
          exact hSurv hh.1.2
        simp only [if_pos hdiv, if_neg hCond, f, hproxy, mul_zero]
    · have hCond : ¬ ((p ∣ 2 * u + 1 ∧
          (∀ q ∈ (primesUpTo (Analytic.W x)).erase 2,
            ¬ q ∣ 2 * u + 1)) ∧ C.weighted x jstar u ≠ 0) := by
        intro hh
        exact hdiv hh.1.1
      simp only [if_neg hdiv, if_neg hCond, f]
  rw [hPair]
  unfold primeDivisorProxySiftedMass
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro u hu
  exact hterm u p hp

/-- Bound a prime-bin divisor proxy sum by its density main term and the
depth-refined fixed-prime sieve remainder. -/
theorem roughProxyDivisorProxySum_refined_upper
    (B : BlockSieve) (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (γ γ' S Q θ Kdens : ℝ) (K : ℕ)
    (hX : 1 < x) (hW : 1 ≤ Analytic.W x)
    (hWγ : Analytic.W x ≤ x ^ γ)
    (hγ : 0 < γ) (hγ' : 0 < γ') (hQ : 0 ≤ Q)
    (hKdens : 0 < Kdens)
    (hInterval : ∀ w : ℝ, 1 < w →
      (∑ q ∈ ((primesUpTo (w ^ 2)).filter (fun q : ℕ => w < (q : ℝ))),
        1 / ((q : ℝ) - 1)) ≤ Kdens)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : 0 ≤ C.mass x jstar)
    (hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hDensity : ∀ (m n u : ℕ), m * n = 2 * u + 1 →
      x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
      γ < Real.log (n : ℝ) / Analytic.L x →
      Real.log (n : ℝ) / Analytic.L x ≤ γ' →
      proxyConstant (.rough γ) x S m ≤ Q)
    (hY : 2 ≤ Analytic.W x) :
    let M := Finset.Ico 1 (2 ^ K)
    let U := Finset.Icc 1 ⌊2 * x⌋₊
    let isBin := fun p : ℕ => Nat.Prime p ∧
      x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
    let P := M.filter isBin
    let T := (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1)
    ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
      ∀ h : ℕ, h₀ ≤ h → Even h →
        (∀ p ∈ P, ∀ d ∈ smallSieveModuli (Analytic.W x)
            ((Analytic.W x) ^ (4 * h + 2)),
          (p * d : ℝ) ≤ x ^ θ) →
        (∑ z ∈ T, C.weighted x jstar z.1 *
          proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) ≤
          Q * ((1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
            shiftedSieveProduct (Analytic.W x) *
              (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
            Kblock *
              (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                  (fun e => Odd e ∧ Squarefree e)),
                |C.remainder x jstar e|)) := by
  classical
  dsimp
  let M := Finset.Ico 1 (2 ^ K)
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let isBin := fun p : ℕ => Nat.Prime p ∧
    x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ'
  let P := M.filter isBin
  let T := (U ×ˢ P).filter (fun z => z.2 ∣ 2 * z.1 + 1)
  have hpPrime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  have hpBin : ∀ p ∈ P, x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.2
  have hpLarge : ∀ p ∈ P, Analytic.W x < (p : ℝ) := by
    intro p hp
    exact lt_of_le_of_lt hWγ (hpBin p hp).1
  have hProxyEq :
      (∑ z ∈ T, C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) =
        ∑ p ∈ P, primeDivisorProxySiftedMass C x jstar p
          (Analytic.W x) γ S := by
    simpa [U, T] using roughProxyDivisorProxySum_eq_fixedPrime
      C x jstar γ γ' S P hpPrime hpBin hW hWγ
  have hProxy := primeBinProxySiftedMass_sum_le C x jstar P γ γ' S Q
    hX hW hγ hγ' hweight hSupport hpPrime hpBin hDensity
  have hxNonneg : 0 ≤ x := by linarith
  obtain ⟨Kblock, hKblock, h₀, hSieve⟩ :=
    primeDivisorSiftedMass_sum_refined_upper B C x jstar
      (Analytic.W x) θ Kdens P hxNonneg hY hKdens hInterval
      hweight hmass hpPrime hpLarge
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  intro h hh heven hLevel
  have hSieveBound := hSieve h hh heven hLevel
  calc
    (∑ z ∈ T, C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) =
        ∑ p ∈ P, primeDivisorProxySiftedMass C x jstar p
          (Analytic.W x) γ S := hProxyEq
    _ ≤ Q * (∑ p ∈ P, primeDivisorSiftedMass C x jstar p (Analytic.W x)) :=
      hProxy
    _ ≤ Q * ((1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
          shiftedSieveProduct (Analytic.W x) *
            (∑ p ∈ P, 1 / ((p : ℝ) - 1)) +
          Kblock *
            (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                (fun e => Odd e ∧ Squarefree e)),
              |C.remainder x jstar e|)) :=
      mul_le_mul_of_nonneg_left hSieveBound hQ

/-- An eventual version of the proxy-bin estimate, with sieve constants
uniform across all sufficiently large `x`. -/
theorem roughProxyDivisorProxySum_refined_upper_eventually
    (B : BlockSieve) (C : CandidateData) (jstar : ℕ)
    (γ γ' S θ Kdens : ℝ) (Q : ℝ → ℝ) (P : ℝ → Finset ℕ)
    (hγ : 0 < γ) (hγ' : 0 < γ') (hγ'θ : γ' < θ)
    (hKdens : 0 < Kdens)
    (hInterval : ∀ w : ℝ, 1 < w →
      (∑ q ∈ ((primesUpTo (w ^ 2)).filter (fun q : ℕ => w < (q : ℝ))),
        1 / ((q : ℝ) - 1)) ≤ Kdens)
    (hpPrime : ∀ x p, p ∈ P x → Nat.Prime p)
    (hpBin : ∀ x p, p ∈ P x →
      x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ')
    (hX : ∀ᶠ x : ℝ in atTop, 1 < x)
    (hW1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.W x)
    (hWγ : ∀ᶠ x : ℝ in atTop, Analytic.W x ≤ x ^ γ)
    (hY2 : ∀ᶠ x : ℝ in atTop, 2 ≤ Analytic.W x)
    (hQ : ∀ᶠ x : ℝ in atTop, 0 ≤ Q x)
    (hweight : ∀ᶠ x : ℝ in atTop,
      ∀ u, 0 ≤ C.weighted x jstar u)
    (hmass : ∀ᶠ x : ℝ in atTop, 0 ≤ C.mass x jstar)
    (hSupport : ∀ᶠ x : ℝ in atTop,
      ∀ u, C.weighted x jstar u ≠ 0 →
        x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hDensity : ∀ᶠ x : ℝ in atTop,
      ∀ (m n u : ℕ), m * n = 2 * u + 1 →
        x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
        γ < Real.log (n : ℝ) / Analytic.L x →
        Real.log (n : ℝ) / Analytic.L x ≤ γ' →
        proxyConstant (.rough γ) x S m ≤ Q x) :
    ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
      ∀ h : ℕ, h₀ ≤ h → Even h →
        ∀ᶠ x : ℝ in atTop,
          (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ P x).filter
              (fun z => z.2 ∣ 2 * z.1 + 1)),
            C.weighted x jstar z.1 *
              proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) ≤
            Q x * ((1 + Kblock * Real.exp (-(h : ℝ))) *
                C.mass x jstar * shiftedSieveProduct (Analytic.W x) *
                  (∑ p ∈ P x, 1 / ((p : ℝ) - 1)) +
              Kblock *
                (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                    (fun e => Odd e ∧ Squarefree e)),
                  |C.remainder x jstar e|)) := by
  have hSieve := primeDivisorSiftedMass_sum_refined_upper_family
    B C jstar Analytic.W P θ Kdens hKdens hInterval hpPrime
  obtain ⟨Kblock, hKblock, h₀, hSieve⟩ := hSieve
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  intro h hh heven
  have hLevelBase := eventually_prime_bin_modulus_level γ' θ h hγ'θ
  have hLevel : ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ P x, ∀ d ∈ smallSieveModuli (Analytic.W x)
        ((Analytic.W x) ^ (4 * h + 2)),
        (p * d : ℝ) ≤ x ^ θ := by
    filter_upwards [hLevelBase] with x hx
    intro p hp d hd
    exact hx p (hpPrime x p hp) (hpBin x p hp).2 d hd
  filter_upwards [hX, hW1, hWγ, hY2, hQ, hweight, hmass,
    hSupport, hDensity, hLevel] with x hx hYone hWY hYtwo hQx
      hweights hmassx hsupport hdensity hlevel
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let T := (U ×ˢ P x).filter (fun z => z.2 ∣ 2 * z.1 + 1)
  have hpLarge : ∀ p ∈ P x, Analytic.W x < (p : ℝ) := by
    intro p hp
    exact lt_of_le_of_lt hWY (hpBin x p hp).1
  have hxNonneg : 0 ≤ x := by linarith
  have hSieveBound := hSieve h hh heven x hxNonneg hYtwo hpLarge
    hweights hmassx hlevel
  have hProxyEq :
      (∑ z ∈ T, C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) =
        ∑ p ∈ P x, primeDivisorProxySiftedMass C x jstar p
          (Analytic.W x) γ S := by
    simpa [U, T] using roughProxyDivisorProxySum_eq_fixedPrime
      C x jstar γ γ' S (P x) (hpPrime x) (hpBin x) hYone hWY
  have hProxy := primeBinProxySiftedMass_sum_le C x jstar (P x)
    γ γ' S (Q x) hx hYone hγ hγ' hweights hsupport
    (hpPrime x) (hpBin x) hdensity
  calc
    (∑ z ∈ T, C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) =
        ∑ p ∈ P x, primeDivisorProxySiftedMass C x jstar p
          (Analytic.W x) γ S := hProxyEq
    _ ≤ Q x * (∑ p ∈ P x,
          primeDivisorSiftedMass C x jstar p (Analytic.W x)) := hProxy
    _ ≤ Q x * ((1 + Kblock * Real.exp (-(h : ℝ)))*
          C.mass x jstar * shiftedSieveProduct (Analytic.W x) *
            (∑ p ∈ P x, 1 / ((p : ℝ) - 1)) +
          Kblock *
            (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                (fun e => Odd e ∧ Squarefree e)),
              |C.remainder x jstar e|)) :=
      mul_le_mul_of_nonneg_left hSieveBound hQx

/-- The finite prime set in a fixed exponent bin. It is empty before the
power interval is defined on positive `x`. -/
noncomputable def primeExponentBin (γ γ' x : ℝ) : Finset ℕ :=
  if hx : 3 ≤ x then
    let K := Classical.choose (exists_logarithmic_dyadic_cutoff x hx)
    (Finset.Ico 1 (2 ^ K)).filter (fun p : ℕ =>
      Nat.Prime p ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ')
  else ∅

/-- The supremum of rough cofactor densities on a prime exponent bin. -/
def roughBinDensitySup (γ γ' : ℝ) : ℝ :=
  sSup ((fun a : ℝ => roughDensity γ (1 - a)) '' Set.Icc γ γ')

/-- Rough cofactor density suprema on sub-half bins are nonnegative. -/
theorem roughBinDensitySup_nonneg (γ γ' κ : ℝ)
    (hγ : 0 < γ) (hκ : 0 < κ)
    (hγ' : γ' ≤ 1 / 2 - κ) :
    0 ≤ roughBinDensitySup γ γ' := by
  rw [roughBinDensitySup]
  apply Real.sSup_nonneg
  intro y hy
  rcases (Set.mem_image (fun a : ℝ => roughDensity γ (1 - a))
      (Set.Icc γ γ') y).1 hy with ⟨a, ha, rfl⟩
  have htail : 0 < 1 - a := by
    have ha' := Set.mem_Icc.mp ha
    linarith [hγ', hκ]
  exact roughDensity_nonneg γ (1 - a) hγ htail

/-- Continuity of the rough density on a compact exponent interval bounds
all bin suprema by one finite constant. -/
theorem roughBinDensitySup_bddAbove
    (hp : ProxyInputs) (γ γ' κ : ℝ)
    (hγ : 0 < γ) (hγγ' : γ < γ') (hκ : 0 < κ)
    (hγ' : γ' ≤ 1 / 2 - κ) :
    ∃ M : ℝ, roughBinDensitySup γ γ' ≤ M := by
  let I := Set.Icc γ γ'
  let f := fun a : ℝ => roughDensity γ (1 - a)
  have hmap : ContinuousOn (fun a : ℝ => (γ, 1 - a)) I := by
    fun_prop
  have hmaps : Set.MapsTo (fun a : ℝ => (γ, 1 - a)) I
      {v : ℝ × ℝ | 0 < v.1 ∧ v.1 < v.2} := by
    intro a ha
    have ha' := Set.mem_Icc.mp ha
    change 0 < γ ∧ γ < 1 - a
    constructor
    · exact hγ
    · have hhalf : γ' < 1 / 2 := by linarith [hκ, hγ']
      have hahalf : a < 1 / 2 := lt_of_le_of_lt ha'.2 hhalf
      linarith
  have hcont : ContinuousOn f I := by
    have h := hp.identities.1.comp' hmap hmaps
    simpa [f, Function.comp_def] using h
  have hbounded : BddAbove (f '' I) := isCompact_Icc.bddAbove_image hcont
  obtain ⟨M, hM⟩ := hbounded
  have hIne : (f '' I).Nonempty := by
    refine ⟨f γ, ?_⟩
    exact Set.mem_image_of_mem f ⟨le_rfl, hγγ'.le⟩
  refine ⟨M, ?_⟩
  rw [roughBinDensitySup]
  exact csSup_le hIne hM

/-- The pointwise proxy coefficient supplied by `ProxyInputs` on a bin. -/
def roughBinProxyCoefficient (γ γ' ε x : ℝ) : ℝ :=
  (roughBinDensitySup γ γ' + ε) /
    (Analytic.L x * sieveProduct (Analytic.W x))

/-- Cancel the ordinary sieve product in the proxy coefficient against the
shifted product in the fixed-prime main term. -/
theorem roughBinProxyCoefficient_shiftedProduct_eq
    (γ γ' ε x : ℝ) (hL : 0 < Analytic.L x) :
    roughBinProxyCoefficient γ γ' ε x * shiftedSieveProduct (Analytic.W x) =
      (roughBinDensitySup γ γ' + ε) / Analytic.L x *
        (shiftedSieveProduct (Analytic.W x) /
          sieveProduct (Analytic.W x)) := by
  unfold roughBinProxyCoefficient
  field_simp [ne_of_gt hL, ne_of_gt (sieveProduct_pos (Analytic.W x))]
  <;> ring

/-- The bin proxy coefficient is eventually bounded by a fixed constant. -/
theorem eventually_roughBinProxyCoefficient_le
    (hc : ClassicalInputs) (hp : ProxyInputs)
    (γ γ' κ ε : ℝ) (hγ : 0 < γ) (hγγ' : γ < γ')
    (hκ : 0 < κ) (hγ' : γ' ≤ 1 / 2 - κ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      roughBinProxyCoefficient γ γ' ε x ≤
        roughBinDensitySup γ γ' + ε := by
  have hden := eventually_one_le_log_sieveProduct_W hc
  filter_upwards [hden] with x hden
  have hdenPos : 0 < Analytic.L x * sieveProduct (Analytic.W x) :=
    lt_of_lt_of_le zero_lt_one hden
  have hnum : 0 ≤ roughBinDensitySup γ γ' + ε := by
    linarith [roughBinDensitySup_nonneg γ γ' κ hγ hκ hγ']
  apply (div_le_iff₀ hdenPos).2
  calc
    roughBinDensitySup γ γ' + ε =
        (roughBinDensitySup γ γ' + ε) * 1 := by ring
    _ ≤ (roughBinDensitySup γ γ' + ε) *
          (Analytic.L x * sieveProduct (Analytic.W x)) :=
      mul_le_mul_of_nonneg_left hden hnum

/-- The shifted reciprocal-prime mass of the cutoff finite bin is bounded by
the mass of the full power interval. -/
theorem eventually_primeExponentBin_reciprocal_le
    (hc : ClassicalInputs) (γ γ' ε : ℝ)
    (hγ : 0 < γ) (hγγ' : γ < γ') (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ primeExponentBin γ γ' x, 1 / ((p : ℝ) - 1)) ≤
        Real.log (γ' / γ) + ε := by
  have hfull := eventually_shifted_prime_reciprocal_power_interval_le
    hc γ γ' ε hγ hγγ' hε
  filter_upwards [hfull, eventually_ge_atTop (3 : ℝ)] with x hfull hx
  let Pfull := (primesUpTo (x ^ γ')).filter (fun p : ℕ => x ^ γ < (p : ℝ))
  have hsubset : primeExponentBin γ γ' x ⊆ Pfull := by
    intro p hp
    have hpP : p ∈ (Finset.Ico 1
        (2 ^ Classical.choose (exists_logarithmic_dyadic_cutoff x hx))).filter
          (fun p : ℕ => Nat.Prime p ∧
            x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ') := by
      simpa [primeExponentBin, hx] using hp
    rcases Finset.mem_filter.mp hpP with ⟨_, hpData⟩
    rcases hpData with ⟨hpPrime, hpLo, hpHi⟩
    have hpowNonneg : 0 ≤ x ^ γ' := Real.rpow_nonneg (by linarith) _
    have hpUp : p ∈ primesUpTo (x ^ γ') :=
      (mem_primesUpTo_iff (x ^ γ') hpowNonneg p).2 ⟨hpPrime, hpHi⟩
    change p ∈ Pfull
    exact Finset.mem_filter.mpr ⟨hpUp, hpLo⟩
  have hpowNonneg : 0 ≤ x ^ γ' := Real.rpow_nonneg (by linarith) _
  have hsum :
      (∑ p ∈ primeExponentBin γ γ' x, 1 / ((p : ℝ) - 1)) ≤
        ∑ p ∈ Pfull, 1 / ((p : ℝ) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp hnot
    have hpPrime : Nat.Prime p :=
      (mem_primesUpTo_iff (x ^ γ') hpowNonneg p).1
        (Finset.mem_filter.mp hp).1 |>.1
    have hpCast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
    exact div_nonneg (by norm_num) (by linarith)
  exact le_trans hsum hfull

/-- Convert one bin's proxy sieve main term into its density supremum times
the singular-series and reciprocal-prime factors. -/
theorem roughBinProxyMain_le
    (hp : ProxyInputs) (γ γ' ε x Kblock : ℝ) (hKblock : 0 ≤ Kblock)
    (h : ℕ)
    (mass reciprocal ηratio ηrecip : ℝ)
    (hγ : 0 < γ) (hγγ' : γ < γ')
    (hε : 0 < ε)
    (hL : 0 < Analytic.L x) (hmass : 0 ≤ mass)
    (hA : 0 ≤ roughBinDensitySup γ γ')
    (hrecip : 0 ≤ reciprocal)
    (hRatioUpper :
      shiftedSieveProduct (Analytic.W x) / sieveProduct (Analytic.W x) ≤
        singularSeries + ηratio)
    (hRecipUpper : reciprocal ≤ Real.log (γ' / γ) + ηrecip)
    (hηratio : 0 ≤ ηratio) (hηrecip : 0 ≤ ηrecip) :
    roughBinProxyCoefficient γ γ' ε x *
        ((1 + Kblock * Real.exp (-(h : ℝ))) * mass *
          shiftedSieveProduct (Analytic.W x) * reciprocal) ≤
      (1 + Kblock * Real.exp (-(h : ℝ))) * mass / Analytic.L x *
        (roughBinDensitySup γ γ' + ε) *
          (singularSeries + ηratio) *
            (Real.log (γ' / γ) + ηrecip) := by
  have hV : 0 < sieveProduct (Analytic.W x) := sieveProduct_pos _
  have hShift : 0 < shiftedSieveProduct (Analytic.W x) :=
    shiftedSieveProduct_pos _
  have hlogratio : 0 < Real.log (γ' / γ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hγ]
    simpa using hγγ'
  have hSing : 0 ≤ singularSeries + ηratio := by
    linarith [hp.products.1]
  have hLog : 0 ≤ Real.log (γ' / γ) + ηrecip := by
    linarith
  have hCoeff : 0 ≤ (roughBinDensitySup γ γ' + ε) / Analytic.L x :=
    div_nonneg (by linarith) hL.le
  have hMain : 0 ≤ 1 + Kblock * Real.exp (-(h : ℝ)) :=
    add_nonneg (by norm_num) (mul_nonneg hKblock (Real.exp_nonneg _))
  have hCore : 0 ≤ (1 + Kblock * Real.exp (-(h : ℝ))) * mass *
      ((roughBinDensitySup γ γ' + ε) / Analytic.L x) :=
    mul_nonneg (mul_nonneg hMain hmass) hCoeff
  have hCoeffEq := roughBinProxyCoefficient_shiftedProduct_eq
    γ γ' ε x hL
  calc
    _ = (1 + Kblock * Real.exp (-(h : ℝ))) * mass *
          (roughBinProxyCoefficient γ γ' ε x *
            shiftedSieveProduct (Analytic.W x)) * reciprocal := by ring
    _ = (1 + Kblock * Real.exp (-(h : ℝ))) * mass *
          ((roughBinDensitySup γ γ' + ε) / Analytic.L x *
            (shiftedSieveProduct (Analytic.W x) /
              sieveProduct (Analytic.W x))) * reciprocal := by
          rw [hCoeffEq]
    _ = (1 + Kblock * Real.exp (-(h : ℝ))) * mass *
          ((roughBinDensitySup γ γ' + ε) / Analytic.L x) *
          (shiftedSieveProduct (Analytic.W x) /
            sieveProduct (Analytic.W x)) * reciprocal := by ring
    _ ≤ (1 + Kblock * Real.exp (-(h : ℝ))) * mass *
          ((roughBinDensitySup γ γ' + ε) / Analytic.L x) *
          (singularSeries + ηratio) * reciprocal := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hRatioUpper hCore
          · exact hrecip
    _ ≤ (1 + Kblock * Real.exp (-(h : ℝ))) * mass *
          ((roughBinDensitySup γ γ' + ε) / Analytic.L x) *
          (singularSeries + ηratio) *
            (Real.log (γ' / γ) + ηrecip) := by
          apply mul_le_mul_of_nonneg_left hRecipUpper
          exact mul_nonneg hCore hSing
    _ = _ := by ring

/-- Instantiate the eventual proxy-bin sieve bound from `ProxyInputs` and
the candidate's support and nonnegativity bounds. -/
theorem eventually_prime_bin_proxy_upper
    (hc : ClassicalInputs) (hs : SieveInputs) (hp : ProxyInputs)
    (C : CandidateData) (δ : ℝ) (hBounds : C.Bounds δ)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (b κ γ γ' S θ ε : ℝ)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hbg : b ≤ γ) (hγ : 0 < γ) (hγ' : 0 < γ')
    (hγlt : γ < γ') (hγtop : γ' ≤ 1 / 2 - κ)
    (hS : 0 < S) (hε : 0 < ε) (hγθ : γ' < θ) :
    ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
      ∀ h : ℕ, h₀ ≤ h → Even h →
        ∀ᶠ x : ℝ in atTop,
          (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
              primeExponentBin γ γ' x).filter
                (fun z => z.2 ∣ 2 * z.1 + 1)),
            C.weighted x jstar z.1 *
              proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) ≤
            roughBinProxyCoefficient γ γ' ε x *
              ((1 + Kblock * Real.exp (-(h : ℝ))) *
                  C.mass x jstar * shiftedSieveProduct (Analytic.W x) *
                    (∑ p ∈ primeExponentBin γ γ' x,
                      1 / ((p : ℝ) - 1)) +
                Kblock *
                  (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                      (fun e => Odd e ∧ Squarefree e)),
                    |C.remainder x jstar e|)) := by
  classical
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩
  have hpPrime : ∀ x p, p ∈ primeExponentBin γ γ' x → Nat.Prime p := by
    intro x p hpP
    by_cases hx : 3 ≤ x
    · have hpP' : p ∈ (Finset.Ico 1
          (2 ^ Classical.choose (exists_logarithmic_dyadic_cutoff x hx))).filter
            (fun p : ℕ => Nat.Prime p ∧
              x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ') := by
        simpa [primeExponentBin, hx] using hpP
      exact (Finset.mem_filter.mp hpP').2.1
    · simp [primeExponentBin, hx] at hpP
  have hpBin : ∀ x p, p ∈ primeExponentBin γ γ' x →
      x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' := by
    intro x p hpP
    by_cases hx : 3 ≤ x
    · have hpP' : p ∈ (Finset.Ico 1
          (2 ^ Classical.choose (exists_logarithmic_dyadic_cutoff x hx))).filter
            (fun p : ℕ => Nat.Prime p ∧
              x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ') := by
        simpa [primeExponentBin, hx] using hpP
      have hpData := (Finset.mem_filter.mp hpP').2
      exact ⟨hpData.2.1, hpData.2.2⟩
    · simp [primeExponentBin, hx] at hpP
  let Q := roughBinProxyCoefficient γ γ' ε
  have hX : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  have hW1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.W x := by
    filter_upwards [eventually_two_le_W] with x hx
    exact le_trans (by norm_num) hx
  have hWγ : ∀ᶠ x : ℝ in atTop, Analytic.W x ≤ x ^ γ :=
    eventually_W_le_rpow γ hγ
  have hY2 : ∀ᶠ x : ℝ in atTop, 2 ≤ Analytic.W x := eventually_two_le_W
  have hA : 0 ≤ roughBinDensitySup γ γ' := by
    rw [roughBinDensitySup]
    apply Real.sSup_nonneg
    intro y hy
    rcases (Set.mem_image (fun a : ℝ => roughDensity γ (1 - a))
        (Set.Icc γ γ') y).1 hy with ⟨a, ha, rfl⟩
    have ha' := Set.mem_Icc.mp ha
    have htail : 0 < 1 - a := by linarith [hγtop, hκ]
    exact roughDensity_nonneg γ (1 - a) hγ htail
  have hQ : ∀ᶠ x : ℝ in atTop, 0 ≤ Q x := by
    filter_upwards [hX] with x hx
    have hL : 0 < Analytic.L x := by
      dsimp [Analytic.L]
      exact Real.log_pos hx
    have hden : 0 < Analytic.L x * sieveProduct (Analytic.W x) :=
      mul_pos hL (sieveProduct_pos _)
    dsimp [Q, roughBinProxyCoefficient]
    exact div_nonneg (by linarith [hA, hε]) hden.le
  obtain ⟨Kdens, hKdens, hInterval⟩ :=
    shifted_prime_density_interval_bound_all hc
  have hDensity := proxy_rough_bin_density_event hp b κ S γ γ' ε
    hb hκ hκsmall hS hbg hγlt hγtop hε
  have hBoundEvent := hBound jstar hjstar
  have hweight : ∀ᶠ x : ℝ in atTop,
      ∀ u, 0 ≤ C.weighted x jstar u := by
    filter_upwards [hBoundEvent] with x hx
    rcases hx with ⟨_, _, _, hweights, _, _⟩
    exact hweights
  have hmass : ∀ᶠ x : ℝ in atTop, 0 ≤ C.mass x jstar := by
    filter_upwards [hBoundEvent, hX] with x hx hxgt
    rcases hx with ⟨hMassLower, _, _, _, _, _⟩
    have hx0 : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 1) hxgt.le
    have hLpos : 0 < Analytic.L x := by
      dsimp [Analytic.L]
      exact Real.log_pos hxgt
    exact le_trans (mul_nonneg hx0 (Real.rpow_nonneg hLpos.le _)) hMassLower
  have hSupport : ∀ᶠ x : ℝ in atTop,
      ∀ u, C.weighted x jstar u ≠ 0 →
        x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x := by
    filter_upwards [hBoundEvent] with x hx
    rcases hx with ⟨_, _, _, _, _, hSupp⟩
    intro u hu
    rcases hSupp u hu with ⟨hlo, hhi, _⟩
    exact ⟨hlo, hhi⟩
  have hSieve := roughProxyDivisorProxySum_refined_upper_eventually
    hs.block C jstar γ γ' S θ Kdens Q (fun x => primeExponentBin γ γ' x)
    hγ hγ' hγθ hKdens hInterval hpPrime hpBin hX hW1 hWγ hY2 hQ
    hweight hmass hSupport (by
      simpa [Q, roughBinProxyCoefficient, roughBinDensitySup] using hDensity)
  simpa [Q, roughBinProxyCoefficient, primeExponentBin] using hSieve

/-- Sum the per-box Type II error over the full dyadic grid. -/
theorem typeII_unbalanced_pair_error_boxsum_bound
    (hII : TypeIIEstimate) (hp : ProxyInputs) (C : CandidateData) (δ : ℝ)
    (hBounds : C.Bounds δ) (hValid : C.bands.Valid)
    (hPsi : ContDiff ℝ ∞ C.psi)
    (hPsiSupport : Function.support C.psi ⊆ Set.Icc 1 2)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (Dsave bstar b κ γ γ' : ℝ)
    (hDsave : 0 < Dsave) (hbstar : 0 < bstar)
    (hbstarSmall : bstar < 1 / 2) (hbstarEq : b = 3 * bstar)
    (hslot : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hγ : b ≤ γ) (hγlt : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ S : ℝ, 2 * B + 3 < S → ∀ᶠ x : ℝ in atTop,
        ∀ N : ℕ,
          |roughProxyErrorPairSum C x jstar γ γ' S N| ≤
            (N : ℝ) ^ 2 * (K * x * Analytic.L x ^ (-Dsave)) := by
  obtain ⟨B, K, hB, hK, hBoxEvent⟩ :=
    typeII_unbalanced_box_bound hII hp C δ hBounds hValid hPsi hPsiSupport
      jstar hjstar Dsave bstar b κ γ γ' hDsave hbstar hbstarSmall hbstarEq
      hslot hb hκ hκsmall hγ hγlt hγ'
  refine ⟨B, K, hB, hK, ?_⟩
  intro S hS
  have hXEvent : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  have hLogEvent : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.L x := by
    simpa [Analytic.L] using Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [hBoxEvent S hS, hXEvent, hLogEvent]
    with x hBoxBound hx hL
  intro N
  let s : Finset (ℕ × ℕ) := Finset.range N ×ˢ Finset.range N
  let f : ℕ × ℕ → ℝ := fun z =>
    roughProxyErrorBox C.bands x jstar C.psi γ γ' S (2 ^ z.1) (2 ^ z.2)
  let E : ℝ := K * x * Analytic.L x ^ (-Dsave)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hf : ∀ z ∈ s, |f z| ≤ E := by
    intro z hz
    have hmem := Finset.mem_product.mp hz
    have hmemLeft := Finset.mem_range.mp hmem.1
    have hmemRight := Finset.mem_range.mp hmem.2
    exact hBoxBound (2 ^ z.1) (2 ^ z.2)
  have hboxRect :
      (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        roughProxyErrorBox C.bands x jstar C.psi γ γ' S (2 ^ k) (2 ^ l)) =
        ∑ z ∈ s, f z := by
    simpa [s, f] using
      (Finset.sum_product' (Finset.range N) (Finset.range N)
        (fun k l => roughProxyErrorBox C.bands x jstar C.psi γ γ' S (2 ^ k) (2 ^ l))).symm
  have hPairEq : roughProxyErrorPairSum C x jstar γ γ' S N =
      ∑ z ∈ s, f z := by
    rw [roughProxyErrorPairSum_eq_boxes]
    exact hboxRect
  have hcard : (s.card : ℝ) = (N : ℝ) ^ 2 := by
    simp [s, Finset.card_product, Finset.card_range, pow_two]
    <;> ring
  calc
    |roughProxyErrorPairSum C x jstar γ γ' S N| = |∑ z ∈ s, f z| := by rw [hPairEq]
    _ ≤ (s.card : ℝ) * E := abs_sum_le_card_mul_bound s f E hE hf
    _ = (N : ℝ) ^ 2 * (K * x * Analytic.L x ^ (-Dsave)) := by
      rw [hcard]

/-- The actual rough-cofactor mass in one prime bin differs from its proxy
mass by the Type II box error, with the dyadic cutoff cost made explicit. -/
theorem eventually_actual_prime_bin_le_proxy_add_typeII
    (hII : TypeIIEstimate) (hp : ProxyInputs) (C : CandidateData) (δ : ℝ)
    (hBounds : C.Bounds δ) (hValid : C.bands.Valid)
    (hPsi : ContDiff ℝ ∞ C.psi)
    (hPsiSupport : Function.support C.psi ⊆ Set.Icc 1 2)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (Dsave bstar b κ γ γ' : ℝ)
    (hDsave : 0 < Dsave) (hbstar : 0 < bstar)
    (hbstarSmall : bstar < 1 / 2) (hbstarEq : b = 3 * bstar)
    (hslot : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hγ : b ≤ γ) (hγlt : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ S : ℝ, 2 * B + 3 < S → ∀ᶠ x : ℝ in atTop,
        (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
            primeExponentBin γ γ' x).filter
              (fun z => z.2 ∣ 2 * z.1 + 1)),
          C.weighted x jstar z.1 *
            test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
        (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
            primeExponentBin γ γ' x).filter
              (fun z => z.2 ∣ 2 * z.1 + 1)),
          C.weighted x jstar z.1 *
            proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) +
          (3 / Real.log 2 + 1) ^ 2 * K * x *
            Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
  obtain ⟨B, K, hB, hK, hTypeII⟩ :=
    typeII_unbalanced_pair_error_boxsum_bound hII hp C δ hBounds hValid
      hPsi hPsiSupport jstar hjstar Dsave bstar b κ γ γ' hDsave hbstar
      hbstarSmall hbstarEq hslot hb hκ hκsmall hγ hγlt hγ'
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩
  have hSupportEvent : ∀ᶠ x : ℝ in atTop,
      ∀ u, C.weighted x jstar u ≠ 0 →
        x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x := by
    have hData := hBound jstar hjstar
    filter_upwards [hData] with x hx
    rcases hx with ⟨_, _, _, _, _, hSupp⟩
    intro u hu
    rcases hSupp u hu with ⟨hlo, hhi, _⟩
    exact ⟨hlo, hhi⟩
  refine ⟨B, K, hB, hK, ?_⟩
  intro S hS
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.L x := by
    simpa [Analytic.L] using Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hCutX : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  filter_upwards [hTypeII S hS, hL, hCutX, hSupportEvent]
    with x hErr hLx hx hSupport
  let Kcut := Classical.choose (exists_logarithmic_dyadic_cutoff x hx)
  have hCutSpec := Classical.choose_spec (exists_logarithmic_dyadic_cutoff x hx)
  have hCut : 5 * x < ((2 ^ Kcut : ℕ) : ℝ) := hCutSpec.1
  have hKindex : (Kcut : ℝ) ≤ (3 / Real.log 2) * Analytic.L x + 1 := by
    dsimp [Kcut]
    exact hCutSpec.2
  have hKle : (Kcut : ℝ) ≤
      (3 / Real.log 2 + 1) * Analytic.L x := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcoeff : 0 ≤ 3 / Real.log 2 := by positivity
    nlinarith [hKindex, hLx, hcoeff]
  have hKnonneg : 0 ≤ (Kcut : ℝ) := Nat.cast_nonneg _
  have hCoef : 0 < 3 / Real.log 2 + 1 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hLnonneg : 0 ≤ Analytic.L x := le_trans (by norm_num) hLx
  have hCLnonneg : 0 ≤ (3 / Real.log 2 + 1) * Analytic.L x :=
    mul_nonneg hCoef.le hLnonneg
  have hKsq : (Kcut : ℝ) ^ 2 ≤
      (3 / Real.log 2 + 1) ^ 2 * (Analytic.L x) ^ 2 := by
    have hfactor := mul_nonneg (sub_nonneg.mpr hKle)
      (add_nonneg hCLnonneg hKnonneg)
    nlinarith [hfactor]
  have hError := hErr Kcut
  have hErrorScaled :
      |roughProxyErrorPairSum C x jstar γ γ' S Kcut| ≤
        (3 / Real.log 2 + 1) ^ 2 * K * x *
          Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
    calc
      _ ≤ (Kcut : ℝ) ^ 2 * (K * x * Analytic.L x ^ (-Dsave)) := hError
      _ ≤ ((3 / Real.log 2 + 1) ^ 2 * (Analytic.L x) ^ 2) *
            (K * x * Analytic.L x ^ (-Dsave)) :=
          mul_le_mul_of_nonneg_right hKsq (by positivity)
      _ = _ := by ring
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let T := (U ×ˢ primeExponentBin γ γ' x).filter
    (fun z => z.2 ∣ 2 * z.1 + 1)
  have hSplit : roughProxyErrorPairSum C x jstar γ γ' S Kcut =
      (∑ z ∈ T, C.weighted x jstar z.1 *
        test (.rough γ) x ((2 * z.1 + 1) / z.2)) -
      ∑ z ∈ T, C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2) := by
    simpa [primeExponentBin, hx, Kcut, U, T] using
      roughProxyErrorPairSum_eq_actual_sub_proxy C x jstar γ γ' S Kcut
        hx hCut hSupport
  have hActualLe :
      (∑ z ∈ T, C.weighted x jstar z.1 *
        test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
      (∑ z ∈ T, C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) +
        |roughProxyErrorPairSum C x jstar γ γ' S Kcut| := by
    rw [hSplit]
    have hAbs := le_abs_self
      ((∑ z ∈ T, C.weighted x jstar z.1 *
          test (.rough γ) x ((2 * z.1 + 1) / z.2)) -
        ∑ z ∈ T, C.weighted x jstar z.1 *
          proxy (.rough γ) x S ((2 * z.1 + 1) / z.2))
    linarith
  calc
    (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
        primeExponentBin γ γ' x).filter
          (fun z => z.2 ∣ 2 * z.1 + 1)),
      C.weighted x jstar z.1 *
        test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
      (∑ z ∈ T, C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) +
        |roughProxyErrorPairSum C x jstar γ γ' S Kcut| := by
          simpa [U, T] using hActualLe
    _ ≤ (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
        primeExponentBin γ γ' x).filter
          (fun z => z.2 ∣ 2 * z.1 + 1)),
      C.weighted x jstar z.1 *
        proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) +
        (3 / Real.log 2 + 1) ^ 2 * K * x *
          Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
          simpa [U, T, add_comm, add_left_comm, add_assoc] using
            (add_le_add_right hErrorScaled
              (∑ z ∈ T, C.weighted x jstar z.1 *
                proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)))

/-- Combine the proxy sieve main term and the Type II comparison error for
one unbalanced prime bin. -/
theorem eventually_actual_prime_bin_sieve_upper
    (hc : ClassicalInputs) (hs : SieveInputs)
    (hII : TypeIIEstimate) (hp : ProxyInputs)
    (C : CandidateData) (δ : ℝ) (hBounds : C.Bounds δ)
    (hValid : C.bands.Valid) (hPsi : ContDiff ℝ ∞ C.psi)
    (hPsiSupport : Function.support C.psi ⊆ Set.Icc 1 2)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (Dsave bstar b κ γ γ' θ ε : ℝ)
    (hDsave : 0 < Dsave) (hbstar : 0 < bstar)
    (hbstarSmall : bstar < 1 / 2) (hbstarEq : b = 3 * bstar)
    (hslot : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hγ : b ≤ γ) (hγlt : γ < γ')
    (hγ' : γ' ≤ 1 / 2 - κ) (hγ'θ : γ' < θ) (hε : 0 < ε) :
    ∃ B KII : ℝ, 0 < B ∧ 0 < KII ∧
      ∀ S : ℝ, 2 * B + 3 < S →
        ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
          ∀ h : ℕ, h₀ ≤ h → Even h →
            ∀ᶠ x : ℝ in atTop,
              (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
                  primeExponentBin γ γ' x).filter
                    (fun z => z.2 ∣ 2 * z.1 + 1)),
                C.weighted x jstar z.1 *
                  test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
                roughBinProxyCoefficient γ γ' ε x *
                  ((1 + Kblock * Real.exp (-(h : ℝ))) *
                      C.mass x jstar * shiftedSieveProduct (Analytic.W x) *
                        (∑ p ∈ primeExponentBin γ γ' x,
                          1 / ((p : ℝ) - 1)) +
                    Kblock *
                      (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                          (fun e => Odd e ∧ Squarefree e)),
                        |C.remainder x jstar e|)) +
                  (3 / Real.log 2 + 1) ^ 2 * KII * x *
                    Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
  obtain ⟨B, KII, hB, hKII, hActual⟩ :=
    eventually_actual_prime_bin_le_proxy_add_typeII hII hp C δ hBounds
      hValid hPsi hPsiSupport jstar hjstar Dsave bstar b κ γ γ' hDsave
      hbstar hbstarSmall hbstarEq hslot hb hκ hκsmall hγ hγlt hγ'
  refine ⟨B, KII, hB, hKII, ?_⟩
  intro S hS
  have hγpos : 0 < γ := lt_of_lt_of_le hb hγ
  have hγ'pos : 0 < γ' := lt_trans hγpos hγlt
  have hSpos : 0 < S := by linarith [hB]
  obtain ⟨Kblock, hKblock, h₀, hProxy⟩ :=
    eventually_prime_bin_proxy_upper hc hs hp C δ hBounds jstar hjstar
      b κ γ γ' S θ ε hb hκ hκsmall hγ hγpos hγ'pos hγlt hγ' hSpos hε hγ'θ
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  intro h hh heven
  have hActualEvent := hActual S hS
  have hProxyEvent := hProxy h hh heven
  filter_upwards [hActualEvent, hProxyEvent] with x hA hP
  calc
    (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
        primeExponentBin γ γ' x).filter
          (fun z => z.2 ∣ 2 * z.1 + 1)),
      C.weighted x jstar z.1 *
        test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
      (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
        primeExponentBin γ γ' x).filter
          (fun z => z.2 ∣ 2 * z.1 + 1)),
        C.weighted x jstar z.1 *
          proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) +
        (3 / Real.log 2 + 1) ^ 2 * KII * x *
          Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := hA
    _ ≤ roughBinProxyCoefficient γ γ' ε x *
          ((1 + Kblock * Real.exp (-(h : ℝ))) *
              C.mass x jstar * shiftedSieveProduct (Analytic.W x) *
                (∑ p ∈ primeExponentBin γ γ' x,
                  1 / ((p : ℝ) - 1)) +
            Kblock *
              (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                  (fun e => Odd e ∧ Squarefree e)),
                |C.remainder x jstar e|)) +
          (3 / Real.log 2 + 1) ^ 2 * KII * x *
            Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
          calc
            _ = (3 / Real.log 2 + 1) ^ 2 * KII * x *
                  Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) +
                (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
                    primeExponentBin γ γ' x).filter
                      (fun z => z.2 ∣ 2 * z.1 + 1)),
                  C.weighted x jstar z.1 *
                    proxy (.rough γ) x S ((2 * z.1 + 1) / z.2)) := by ring
            _ ≤ (3 / Real.log 2 + 1) ^ 2 * KII * x *
                  Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) +
                roughBinProxyCoefficient γ γ' ε x *
                  ((1 + Kblock * Real.exp (-(h : ℝ))) *
                      C.mass x jstar * shiftedSieveProduct (Analytic.W x) *
                        (∑ p ∈ primeExponentBin γ γ' x,
                          1 / ((p : ℝ) - 1)) +
                    Kblock *
                      (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                          (fun e => Odd e ∧ Squarefree e)),
                        |C.remainder x jstar e|)) :=
                add_le_add_right hP
                  ((3 / Real.log 2 + 1) ^ 2 * KII * x *
                    Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave))
            _ = _ := by ring

/-- Expand the proxy sieve main term into the bin density supremum, the
singular-series ratio, and the reciprocal prime mass. -/
theorem eventually_actual_prime_bin_density_bound
    (hc : ClassicalInputs) (hs : SieveInputs)
    (hII : TypeIIEstimate) (hp : ProxyInputs)
    (C : CandidateData) (δ : ℝ) (hBounds : C.Bounds δ)
    (hValid : C.bands.Valid) (hPsi : ContDiff ℝ ∞ C.psi)
    (hPsiSupport : Function.support C.psi ⊆ Set.Icc 1 2)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (Dsave bstar b κ γ γ' θ ε ηratio ηrecip : ℝ)
    (hDsave : 0 < Dsave) (hbstar : 0 < bstar)
    (hbstarSmall : bstar < 1 / 2) (hbstarEq : b = 3 * bstar)
    (hslot : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hγ : b ≤ γ) (hγlt : γ < γ')
    (hγ' : γ' ≤ 1 / 2 - κ) (hγ'θ : γ' < θ)
    (hε : 0 < ε) (hηratio : 0 < ηratio) (hηrecip : 0 < ηrecip) :
    ∃ B KII : ℝ, 0 < B ∧ 0 < KII ∧
      ∀ S : ℝ, 2 * B + 3 < S →
        ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
          ∀ h : ℕ, h₀ ≤ h → Even h →
            ∀ᶠ x : ℝ in atTop,
              (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
                  primeExponentBin γ γ' x).filter
                    (fun z => z.2 ∣ 2 * z.1 + 1)),
                C.weighted x jstar z.1 *
                  test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
                (1 + Kblock * Real.exp (-(h : ℝ))) *
                    C.mass x jstar / Analytic.L x *
                      (roughBinDensitySup γ γ' + ε) *
                        (singularSeries + ηratio) *
                          (Real.log (γ' / γ) + ηrecip) +
                  roughBinProxyCoefficient γ γ' ε x * Kblock *
                    (∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
                        (fun e => Odd e ∧ Squarefree e)),
                      |C.remainder x jstar e|) +
                  (3 / Real.log 2 + 1) ^ 2 * KII * x *
                    Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
  obtain ⟨B, KII, hB, hKII, hSieve⟩ :=
    eventually_actual_prime_bin_sieve_upper hc hs hII hp C δ hBounds hValid
      hPsi hPsiSupport jstar hjstar Dsave bstar b κ γ γ' θ ε hDsave
      hbstar hbstarSmall hbstarEq hslot hb hκ hκsmall hγ hγlt hγ' hγ'θ hε
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩
  have hγpos : 0 < γ := lt_of_lt_of_le hb hγ
  have hRatioEvent := eventually_shiftedSieveRatio_W_le hp ηratio hηratio
  have hRecipEvent := eventually_primeExponentBin_reciprocal_le hc γ γ'
    ηrecip hγpos hγlt hηrecip
  have hX : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  have hLpos : ∀ᶠ x : ℝ in atTop, 0 < Analytic.L x := by
    filter_upwards [hX] with x hx
    dsimp [Analytic.L]
    exact Real.log_pos hx
  have hMassNonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ C.mass x jstar := by
    filter_upwards [hBound jstar hjstar, hX] with x hData hx
    rcases hData with ⟨hLower, _, _, _, _, _⟩
    have hx0 : 0 ≤ x := by linarith
    have hL : 0 ≤ Analytic.L x := by
      exact (le_of_lt (Real.log_pos hx))
    exact le_trans (mul_nonneg hx0 (Real.rpow_nonneg hL _)) hLower
  have hA : 0 ≤ roughBinDensitySup γ γ' :=
    roughBinDensitySup_nonneg γ γ' κ hγpos hκ hγ'
  have hRecipNonneg : ∀ x : ℝ,
      0 ≤ ∑ p ∈ primeExponentBin γ γ' x, 1 / ((p : ℝ) - 1) := by
    intro x
    apply Finset.sum_nonneg
    intro p hp
    by_cases hx : 3 ≤ x
    · have hpP : p ∈ (Finset.Ico 1
          (2 ^ Classical.choose (exists_logarithmic_dyadic_cutoff x hx))).filter
          (fun p : ℕ => Nat.Prime p ∧
            x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ') := by
        simpa [primeExponentBin, hx] using hp
      have hpPrime := (Finset.mem_filter.mp hpP).2.1
      have hpCast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
      exact div_nonneg (by norm_num) (by linarith)
    · simp [primeExponentBin, hx] at hp
  refine ⟨B, KII, hB, hKII, ?_⟩
  intro S hS
  obtain ⟨Kblock, hKblock, h₀, hBin⟩ := hSieve S hS
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  intro h hh heven
  have hActual := hBin h hh heven
  filter_upwards [hActual, hRatioEvent, hRecipEvent, hLpos, hMassNonneg]
    with x hActual hRatio hRecip hL hMass
  have hMain := roughBinProxyMain_le hp γ γ' ε x Kblock hKblock.le h
    (C.mass x jstar) (∑ p ∈ primeExponentBin γ γ' x, 1 / ((p : ℝ) - 1))
    ηratio ηrecip hγpos hγlt hε hL hMass hA
    (hRecipNonneg x) hRatio hRecip hηratio.le hηrecip.le
  let R := ∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
      (fun e => Odd e ∧ Squarefree e)), |C.remainder x jstar e|
  have hActualR :
      (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
          primeExponentBin γ γ' x).filter
            (fun z => z.2 ∣ 2 * z.1 + 1)),
        C.weighted x jstar z.1 *
          test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
        roughBinProxyCoefficient γ γ' ε x *
            ((1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
                shiftedSieveProduct (Analytic.W x) *
                  (∑ p ∈ primeExponentBin γ γ' x, 1 / ((p : ℝ) - 1)) +
              Kblock * R) +
          (3 / Real.log 2 + 1) ^ 2 * KII * x *
            Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
    simpa [R] using hActual
  have hActualSplit :
      (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
          primeExponentBin γ γ' x).filter
            (fun z => z.2 ∣ 2 * z.1 + 1)),
        C.weighted x jstar z.1 *
          test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
        roughBinProxyCoefficient γ γ' ε x *
            ((1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
                shiftedSieveProduct (Analytic.W x) *
                  (∑ p ∈ primeExponentBin γ γ' x, 1 / ((p : ℝ) - 1))) +
          roughBinProxyCoefficient γ γ' ε x * Kblock * R +
          (3 / Real.log 2 + 1) ^ 2 * KII * x *
            Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
    calc
      _ ≤ roughBinProxyCoefficient γ γ' ε x *
            ((1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar *
                shiftedSieveProduct (Analytic.W x) *
                  (∑ p ∈ primeExponentBin γ γ' x, 1 / ((p : ℝ) - 1)) +
              Kblock * R) +
            (3 / Real.log 2 + 1) ^ 2 * KII * x *
              Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := hActualR
      _ = _ := by ring
  have hFinal :
      (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
          primeExponentBin γ γ' x).filter
            (fun z => z.2 ∣ 2 * z.1 + 1)),
        C.weighted x jstar z.1 *
          test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
        (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar /
            Analytic.L x * (roughBinDensitySup γ γ' + ε) *
              (singularSeries + ηratio) *
                (Real.log (γ' / γ) + ηrecip) +
          roughBinProxyCoefficient γ γ' ε x * Kblock * R +
          (3 / Real.log 2 + 1) ^ 2 * KII * x *
            Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) := by
    nlinarith [hActualSplit, hMain]
  simpa [R] using hFinal

set_option maxHeartbeats 1000000 in
/-- Absorb the Type I and Type II error terms in a single bin into a small
multiple of candidate mass over `log x`. -/
theorem eventually_actual_prime_bin_density_bound_absorbed
    (hc : ClassicalInputs) (hs : SieveInputs)
    (hII : TypeIIEstimate) (hp : ProxyInputs)
    (C : CandidateData) (δ : ℝ) (hBounds : C.Bounds δ)
    (hTypeI : C.TypeI)
    (hValid : C.bands.Valid) (hPsi : ContDiff ℝ ∞ C.psi)
    (hPsiSupport : Function.support C.psi ⊆ Set.Icc 1 2)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (bstar b κ γ γ' θ ε ηratio ηrecip ηmass : ℝ)
    (hbstar : 0 < bstar) (hbstarSmall : bstar < 1 / 2)
    (hbstarEq : b = 3 * bstar)
    (hslot : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hγ : b ≤ γ) (hγlt : γ < γ')
    (hγ' : γ' ≤ 1 / 2 - κ) (hγ'θ : γ' < θ)
    (hθ : θ < 1 / 2) (hε : 0 < ε)
    (hηratio : 0 < ηratio) (hηrecip : 0 < ηrecip)
    (hηmass : 0 < ηmass) :
    ∃ B KII : ℝ, 0 < B ∧ 0 < KII ∧
      ∀ S : ℝ, 2 * B + 3 < S →
        ∃ Kblock : ℝ, 0 < Kblock ∧ ∃ h₀ : ℕ,
          ∀ h : ℕ, h₀ ≤ h → Even h →
            ∀ᶠ x : ℝ in atTop,
              (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
                  primeExponentBin γ γ' x).filter
                    (fun z => z.2 ∣ 2 * z.1 + 1)),
                C.weighted x jstar z.1 *
                  test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
                (1 + Kblock * Real.exp (-(h : ℝ))) *
                    C.mass x jstar / Analytic.L x *
                      (roughBinDensitySup γ γ' + ε) *
                        (singularSeries + ηratio) *
                          (Real.log (γ' / γ) + ηrecip) +
                  ηmass * C.mass x jstar / Analytic.L x := by
  classical
  let hBoundsFull := hBounds
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩
  let Dsave : ℝ := max 1 (CA + 24)
  have hDsave : 0 < Dsave := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hDsaveLevel : CA + 20 ≤ Dsave := by
    dsimp [Dsave]
    linarith [le_max_right (1 : ℝ) (CA + 24)]
  let Dtype : ℝ := max 1 (CA + 20)
  have hDtype : 0 < Dtype := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hDtypeLevel : CA + 18 ≤ Dtype := by
    dsimp [Dtype]
    linarith [le_max_right (1 : ℝ) (CA + 20)]
  obtain ⟨Ktype, hKtype, hTypeIEvent⟩ :=
    hTypeI θ Dtype hθ hDtype jstar hjstar
  obtain ⟨Mbound, hSupBound⟩ :=
    roughBinDensitySup_bddAbove hp γ γ' κ
      (lt_of_lt_of_le hb hγ) hγlt hκ hγ'
  obtain ⟨B, KII, hB, hKII, hDensityBound⟩ :=
    eventually_actual_prime_bin_density_bound hc hs hII hp C δ hBoundsFull
      hValid hPsi hPsiSupport jstar hjstar Dsave bstar b κ γ γ' θ ε
      ηratio ηrecip hDsave hbstar hbstarSmall hbstarEq hslot hb hκ hκsmall
      hγ hγlt hγ' hγ'θ hε hηratio hηrecip
  have hMassData := hBound jstar hjstar
  have hQBound := eventually_roughBinProxyCoefficient_le hc hp γ γ' κ ε
    (lt_of_lt_of_le hb hγ) hγlt hκ hγ' hε
  have hX : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ Analytic.L x := by
    simpa [Analytic.L] using Real.tendsto_log_atTop.eventually_ge_atTop 1
  refine ⟨B, KII, hB, hKII, ?_⟩
  intro S hS
  obtain ⟨Kblock, hKblock, h₀, hDensity⟩ := hDensityBound S hS
  refine ⟨Kblock, hKblock, h₀, ?_⟩
  let Etype : ℝ := 2 * (Mbound + ε) * Kblock * Ktype
  let Eii : ℝ := (3 / Real.log 2 + 1) ^ 2 * KII
  let Eall : ℝ := Etype + Eii
  have hSupNonneg := roughBinDensitySup_nonneg γ γ' κ
    (lt_of_lt_of_le hb hγ) hκ hγ'
  have hMboundNonneg : 0 ≤ Mbound := le_trans hSupNonneg hSupBound
  have hMplus : 0 ≤ Mbound + ε := by linarith
  have hEall : 0 ≤ Eall := by
    dsimp [Eall, Etype, Eii]
    positivity
  have hEii : 0 ≤ Eii := by dsimp [Eii]; positivity
  have hTailEvent : ∀ᶠ x : ℝ in atTop,
      Eall * Analytic.L x ^ (-17 : ℝ) ≤ ηmass := by
    have hconst : Tendsto (fun _ : ℝ => Eall) atTop (nhds Eall) :=
      tendsto_const_nhds
    have hlogpow :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17)).comp
        Real.tendsto_log_atTop
    have hprod : Tendsto
        (fun x : ℝ => Eall * Analytic.L x ^ (-17 : ℝ)) atTop (nhds 0) := by
      simpa [Analytic.L] using hconst.mul hlogpow
    exact (hprod.eventually (Iio_mem_nhds hηmass)).mono
      (fun x hx => le_of_lt hx)
  intro h hh heven
  have hDensityEvent := hDensity h hh heven
  have hTypeIEvent' := hTypeIEvent
  filter_upwards [hDensityEvent, hTypeIEvent', hMassData, hX, hL,
    hQBound, hTailEvent] with x hDensityx hTypeIx hData hx hLx hQx hTail
  rcases hData with ⟨hMassLower, _, _, _, _, _⟩
  have hx0 : 0 ≤ x := by linarith
  have hLpos : 0 < Analytic.L x := lt_of_lt_of_le zero_lt_one hLx
  have hMass0 : 0 ≤ C.mass x jstar :=
    le_trans (mul_nonneg hx0 (Real.rpow_nonneg hLpos.le _)) hMassLower
  have hQupper : roughBinProxyCoefficient γ γ' ε x ≤ Mbound + ε := by
    linarith [hQx, hSupBound]
  let R := ∑ e ∈ ((Finset.Icc 1 ⌊x ^ θ⌋₊).filter
      (fun e => Odd e ∧ Squarefree e)), |C.remainder x jstar e|
  have hRTypeI : R ≤ Ktype *
      (x * Analytic.L x ^ (-Dtype) +
        C.mass x jstar * Analytic.L x ^ (-18 : ℝ)) := by
    simpa [R] using hTypeIx
  have hMassTailTypeI := x_log_power_tail_le_mass_log18 x (Analytic.L x)
    CA Dtype (C.mass x jstar) hx0 hLx hDtypeLevel hMassLower
  have hRBound : R ≤ 2 * Ktype * C.mass x jstar *
      Analytic.L x ^ (-18 : ℝ) := by
    calc
      R ≤ Ktype * (x * Analytic.L x ^ (-Dtype) +
          C.mass x jstar * Analytic.L x ^ (-18 : ℝ)) := hRTypeI
      _ ≤ Ktype * (2 * C.mass x jstar * Analytic.L x ^ (-18 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith [hMassTailTypeI]) hKtype.le
      _ = _ := by ring
  have hQRem : roughBinProxyCoefficient γ γ' ε x * Kblock * R ≤
      Etype * C.mass x jstar * Analytic.L x ^ (-18 : ℝ) := by
    have hRnonneg : 0 ≤ R := by
      dsimp [R]
      apply Finset.sum_nonneg
      intro e he
      positivity
    calc
      _ = (roughBinProxyCoefficient γ γ' ε x * Kblock) * R := by ring
      _ ≤ ((Mbound + ε) * Kblock) * R := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hQupper hKblock.le) hRnonneg
      _ ≤ (Mbound + ε) * Kblock *
            (2 * Ktype * C.mass x jstar * Analytic.L x ^ (-18 : ℝ)) := by
        have hCoef : 0 ≤ (Mbound + ε) * Kblock :=
          mul_nonneg (by linarith [hSupBound, hε]) hKblock.le
        exact mul_le_mul_of_nonneg_left hRBound hCoef
      _ = _ := by dsimp [Etype]; ring
  have hDsaveTail : CA + 18 ≤ Dsave - 2 := by
    have hD : CA + 20 ≤ Dsave := by
      dsimp [Dsave]
      linarith [le_max_right (1 : ℝ) (CA + 24)]
    linarith
  have hMassTailII := x_log_power_tail_le_mass_log18 x (Analytic.L x) CA
    (Dsave - 2) (C.mass x jstar) hx0 hLx hDsaveTail hMassLower
  have hpowShift : Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave) =
      Analytic.L x ^ (-(Dsave - 2) : ℝ) := by
    have hpowNat : Analytic.L x ^ (2 : ℕ) = Analytic.L x ^ (2 : ℝ) := by
      norm_num
    rw [hpowNat]
    rw [(Real.rpow_add hLpos (2 : ℝ) (-Dsave)).symm]
    congr 1
    ring
  have hTypeIIError :
      (3 / Real.log 2 + 1) ^ 2 * KII * x * Analytic.L x ^ 2 *
          Analytic.L x ^ (-Dsave) ≤
        Eii * C.mass x jstar * Analytic.L x ^ (-18 : ℝ) := by
    calc
      _ = Eii * (x *
          (Analytic.L x ^ 2 * Analytic.L x ^ (-Dsave))) := by
        dsimp [Eii]
        ring
      _ = Eii * (x * Analytic.L x ^ (-(Dsave - 2) : ℝ)) := by
        rw [hpowShift]
      _ ≤ Eii * (C.mass x jstar * Analytic.L x ^ (-18 : ℝ)) :=
        mul_le_mul_of_nonneg_left hMassTailII hEii
      _ = _ := by ring
  have hErrors : roughBinProxyCoefficient γ γ' ε x * Kblock * R +
        (3 / Real.log 2 + 1) ^ 2 * KII * x * Analytic.L x ^ 2 *
          Analytic.L x ^ (-Dsave) ≤
        Eall * C.mass x jstar * Analytic.L x ^ (-18 : ℝ) := by
    calc
      _ ≤ Etype * C.mass x jstar * Analytic.L x ^ (-18 : ℝ) +
            Eii * C.mass x jstar * Analytic.L x ^ (-18 : ℝ) :=
        add_le_add hQRem hTypeIIError
      _ = _ := by dsimp [Eall, Etype, Eii]; ring
  have hAbsorbed := mass_log18_error_le_mass_div_log Eall ηmass
    (C.mass x jstar) (Analytic.L x) hTail hLpos hMass0
  have hErrorsFinal :
      roughBinProxyCoefficient γ γ' ε x * Kblock * R +
          (3 / Real.log 2 + 1) ^ 2 * KII * x * Analytic.L x ^ 2 *
            Analytic.L x ^ (-Dsave) ≤ ηmass * C.mass x jstar / Analytic.L x :=
    le_trans hErrors hAbsorbed
  have hFinal :
      (∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
          primeExponentBin γ γ' x).filter
            (fun z => z.2 ∣ 2 * z.1 + 1)),
        C.weighted x jstar z.1 *
          test (.rough γ) x ((2 * z.1 + 1) / z.2)) ≤
        (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar /
            Analytic.L x * (roughBinDensitySup γ γ' + ε) *
              (singularSeries + ηratio) * (Real.log (γ' / γ) + ηrecip) +
          ηmass * C.mass x jstar / Analytic.L x := by
    calc
      _ ≤ (1 + Kblock * Real.exp (-(h : ℝ))) * C.mass x jstar /
            Analytic.L x * (roughBinDensitySup γ γ' + ε) *
              (singularSeries + ηratio) * (Real.log (γ' / γ) + ηrecip) +
            (roughBinProxyCoefficient γ γ' ε x * Kblock * R +
              (3 / Real.log 2 + 1) ^ 2 * KII * x * Analytic.L x ^ 2 *
                Analytic.L x ^ (-Dsave)) := by
                  simpa [R, add_assoc] using hDensityx
      _ ≤ _ := by nlinarith [hErrorsFinal]
  simpa [R] using hFinal

end Erdos821.P10
end
