import Erdos821.Blueprint.Proxy

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Res
open Blueprint Blueprint.Analytic

/-- Absolute-error residue-class sieve estimate, valid even on tiny subintervals.
Taking r = 1 also supplies the ordinary full-cell denominator estimate. -/
def RoughResidueIntervalTask : Prop :=
  ClassicalInputs → SieveInputs → ∀ b C B A eta : ℝ,
    0 < b → 0 < C → 0 < B → 0 < A → 0 < eta →
    ∀ᶠ x : ℝ in atTop, ∀ lo hi : ℝ, ∀ r a : ℕ,
      x ^ b ≤ lo → lo ≤ hi → hi ≤ x ^ C →
      1 ≤ r → (r : ℝ) ≤ L x ^ B → Nat.Coprime a r →
      |(((Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
          (fun n => rough (W x) n ∧ n % r = a % r)).card : ℝ) -
        (hi - lo) * sieveProduct (W x) / (Nat.totient r : ℝ)| ≤
        (hi - lo) * sieveProduct (W x) / (Nat.totient r : ℝ) * L x ^ (-A) + x ^ eta

lemma floorDiff_error (u v : ℚ) (huv : u ≤ v) :
    |((Int.floor v - Int.floor u : ℤ) : ℝ) - (v - u : ℚ)| ≤ 2 := by
  have hlu : (Int.floor u : ℝ) ≤ u := by exact_mod_cast (Int.floor_le u)
  have huv' : (Int.floor v : ℝ) ≤ v := by exact_mod_cast (Int.floor_le v)
  have huup : u < (Int.floor u : ℝ) + 1 := by exact_mod_cast (Int.lt_floor_add_one u)
  have hvup : v < (Int.floor v : ℝ) + 1 := by exact_mod_cast (Int.lt_floor_add_one v)
  have hfl : Int.floor u ≤ Int.floor v := Int.floor_mono huv
  have hcast : ((v - u : ℚ) : ℝ) = (v : ℝ) - u := by norm_num
  have hupper : ((Int.floor v : ℝ) - Int.floor u) - (v - u) ≤ 2 := by
    linarith
  have hlower : -2 ≤ ((Int.floor v : ℝ) - Int.floor u) - (v - u) := by
    linarith
  rw [abs_le]
  rw [Int.cast_sub, hcast]
  exact ⟨hlower, hupper⟩

lemma apResidueCount_error (u v m c : ℕ) (hm : 0 < m) (huv : u ≤ v) :
    |(((Finset.Ioc u v).filter (fun n => n % m = c % m)).card : ℝ) -
      ((v : ℝ) - u) / m| ≤ 2 := by
  let q₁ : ℚ := ((v : ℚ) - c) / m
  let q₀ : ℚ := ((u : ℚ) - c) / m
  have hq : q₀ ≤ q₁ := by
    dsimp [q₀, q₁]
    have hm' : (0 : ℚ) < m := by positivity
    have hcast : (u : ℚ) ≤ v := by exact_mod_cast huv
    exact (div_le_div_iff_of_pos_right hm').2 (by linarith)
  have hfloor := floorDiff_error q₀ q₁ hq
  have hcard := Nat.Ioc_filter_modEq_card (a := u) (b := v) (r := m) hm c
  have hformula :
      (((Finset.Ioc u v).filter (fun n => n % m = c % m)).card : ℝ) =
        ((Int.floor q₁ - Int.floor q₀ : ℤ) : ℝ) := by
    have hcard' :
        (((Finset.Ioc u v).filter (fun n => n % m = c % m)).card : ℤ) =
          max (Int.floor q₁ - Int.floor q₀) 0 := by
      change (((Finset.Ioc u v).filter (fun n => Nat.ModEq m n c)).card : ℤ) = _
      simpa [q₁, q₀] using hcard
    have hmono : Int.floor q₀ ≤ Int.floor q₁ := Int.floor_mono hq
    have hmax : max (Int.floor q₁ - Int.floor q₀) 0 =
        Int.floor q₁ - Int.floor q₀ := max_eq_left (sub_nonneg.mpr hmono)
    have hc' := congrArg (fun z : ℤ => (z : ℝ)) hcard'
    have hc'' :
        (((Finset.Ioc u v).filter (fun n => n % m = c % m)).card : ℝ) =
          (max (Int.floor q₁ - Int.floor q₀) 0 : ℤ) := by
      simpa only [Int.cast_natCast] using hc'
    rw [hmax] at hc''
    exact hc''
  have hwidth : (q₁ - q₀ : ℚ) = ((v : ℚ) - u) / m := by
    dsimp [q₁, q₀]
    field_simp
    ring
  have hwidthR : ((q₁ - q₀ : ℚ) : ℝ) = ((v : ℝ) - u) / m := by
    calc
      ((q₁ - q₀ : ℚ) : ℝ) = (((v : ℚ) - u) / m) := by exact_mod_cast hwidth
      _ = ((v : ℝ) - u) / m := by norm_num
  rw [hformula, ← hwidthR]
  exact hfloor

lemma apDivResidueCount_error (u v r a d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hcop : Nat.Coprime r d) (huv : u ≤ v) :
    |(((Finset.Ioc u v).filter (fun n => n % r = a % r ∧ d ∣ n)).card : ℝ) -
      ((v : ℝ) - u) / (r * d)| ≤ 2 := by
  let crt := Nat.chineseRemainder hcop a 0
  let c : ℕ := crt.val
  have hc : c ≡ a [MOD r] ∧ c ≡ 0 [MOD d] := by
    exact crt.property
  have hiff (n : ℕ) :
      (n % r = a % r ∧ d ∣ n) ↔ n % (r * d) = c % (r * d) := by
    constructor
    · rintro ⟨hmod, hdvd⟩
      have hmod' : n ≡ a [MOD r] := hmod
      have hdvd' : n ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hdvd
      simpa [Nat.ModEq] using Nat.chineseRemainder_modEq_unique hcop hmod' hdvd'
    · intro hmod'
      have hmod : n ≡ c [MOD r * d] := hmod'
      have hrd : r ∣ r * d := ⟨d, by ring⟩
      have hdd : d ∣ r * d := ⟨r, by ring⟩
      have hm₁ := (Nat.ModEq.of_dvd hrd hmod).trans hc.1
      have hm₂ := (Nat.ModEq.of_dvd hdd hmod).trans hc.2
      exact ⟨hm₁, Nat.modEq_zero_iff_dvd.mp hm₂⟩
  have hfilter :
      (Finset.Ioc u v).filter (fun n => n % r = a % r ∧ d ∣ n) =
        (Finset.Ioc u v).filter (fun n => n % (r * d) = c % (r * d)) := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hn, hp⟩ => ⟨hn, (hiff n).mp hp⟩,
      fun ⟨hn, hp⟩ => ⟨hn, (hiff n).mpr hp⟩⟩
  rw [hfilter]
  simpa only [Nat.cast_mul] using apResidueCount_error u v (r * d) c (by positivity) huv

lemma squarefree_factors_div_iff {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hsq : Squarefree d) :
    (∀ p ∈ d.primeFactors, p ∣ n) ↔ d ∣ n := by
  constructor
  · intro hall
    apply (Nat.factorization_le_iff_dvd hd.ne' hn.ne').1
    intro p
    by_cases hp : p.Prime
    · by_cases hpd : p ∣ d
      · have hpD : p ∈ d.primeFactors := Nat.Prime.mem_primeFactors hp hpd hd.ne'
        rw [Nat.factorization_eq_one_of_squarefree hsq hp hpd]
        exact (hp.dvd_iff_one_le_factorization hn.ne').1 (hall p hpD)
      · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime d hp]
      exact Nat.zero_le _
  · intro hdiv p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans hdiv

lemma mem_primesUpTo {p : ℕ} {z : ℝ} :
    p ∈ primesUpTo z ↔ p.Prime ∧ (p : ℝ) ≤ z := by
  unfold primesUpTo
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp₁, hpz⟩, hp⟩
    exact ⟨hp, (Nat.le_floor_iff' hp.ne_zero).mp hpz⟩
  · rintro ⟨hp, hpz⟩
    exact ⟨⟨by have := hp.two_le; omega,
      (Nat.le_floor_iff' hp.ne_zero).mpr hpz⟩, hp⟩

def apSievePrimes (z : ℝ) (r : ℕ) : Finset ℕ :=
  (primesUpTo z).filter (fun p => ¬ p ∣ r)

def apSieveData (z X lo hi : ℝ) (r a : ℕ) (_hX : 0 ≤ X) : SieveData ℕ where
  objects := (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter (fun n => n % r = a % r)
  weight := fun _ => 1
  primes := apSievePrimes z r
  bad := fun p n => p ∣ n
  X := X
  density := fun p => (p : ℝ)⁻¹
  nonneg := by intro n hn; norm_num
  prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  X_nonneg := _hX

lemma apSieve_prime_not_dvd {z : ℝ} {r p : ℕ} (hp : p ∈ apSievePrimes z r) :
    p.Prime ∧ (p : ℝ) ≤ z ∧ ¬ p ∣ r := by
  rcases Finset.mem_filter.mp hp with ⟨hpz, hnr⟩
  exact ⟨(mem_primesUpTo.mp hpz).1, (mem_primesUpTo.mp hpz).2, hnr⟩

lemma apSieve_factor_coprime {z : ℝ} {r d : ℕ} (hd : 0 < d)
    (hsub : d.primeFactors ⊆ apSievePrimes z r) : Nat.Coprime r d := by
  by_contra hcop
  rw [Nat.Prime.not_coprime_iff_dvd] at hcop
  rcases hcop with ⟨p, hp, hpr, hpd⟩
  have hpf : p ∈ d.primeFactors := hp.mem_primeFactors hpd hd.ne'
  exact (apSieve_prime_not_dvd (hsub hpf)).2.2 hpr

lemma apSieve_remainder_error (z lo hi : ℝ) (r a : ℕ)
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hr : 1 ≤ r)
    (D : ℝ) {d : ℕ}
    (hdmem : d ∈ (apSieveData z ((hi - lo) / r) lo hi r a
      (div_nonneg (sub_nonneg.mpr hlohi) (by positivity))).products D) :
    |(apSieveData z ((hi - lo) / r) lo hi r a
      (div_nonneg (sub_nonneg.mpr hlohi) (by positivity))).remainder d| ≤ 4 := by
  let X : ℝ := (hi - lo) / r
  have hX : 0 ≤ X := by dsimp [X]; positivity
  let S : SieveData ℕ := apSieveData z X lo hi r a hX
  have hdinfo : Squarefree d ∧ d.primeFactors ⊆ apSievePrimes z r := by
    simpa [S, X, SieveData.products, apSieveData] using
      (Finset.mem_filter.mp hdmem).2
  have hdbound : 1 ≤ d := by
    have hmem := (Finset.mem_filter.mp hdmem).1
    exact (Finset.mem_Icc.mp hmem).1
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdbound
  have hcoprd : Nat.Coprime r d := apSieve_factor_coprime hdpos hdinfo.2
  have hlo' : ((1 : ℕ) : ℝ) ≤ lo := by simpa using hlo
  have hflo : (1 : ℕ) ≤ ⌊lo⌋₊ :=
    (Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).mpr hlo'
  have hnpos {n : ℕ} (hn : n ∈ S.objects) : 0 < n := by
    rcases Finset.mem_filter.mp hn with ⟨hnI, _⟩
    have hlt := (Finset.mem_Ioc.mp hnI).1
    omega
  have hsum :
      (∑ n ∈ S.objects, S.weight n * S.monomial d n) =
        ((S.objects.filter (fun n => d ∣ n)).card : ℝ) := by
    calc
      (∑ n ∈ S.objects, S.weight n * S.monomial d n) =
          ∑ n ∈ S.objects, if d ∣ n then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hdiv := squarefree_factors_div_iff hdpos (hnpos hn) hdinfo.1
        simp only [S, SieveData.monomial, SieveData.weight, apSieveData,
          SieveData.bad, one_mul]
        simpa only [hdiv]
      _ = ((S.objects.filter (fun n => d ∣ n)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp
  have hprod : S.g d = (d : ℝ)⁻¹ := by
    calc
      S.g d = ∏ p ∈ d.primeFactors, (p : ℝ)⁻¹ := by
        simp [S, SieveData.g, apSieveData]
      _ = (∏ p ∈ d.primeFactors, (p : ℝ))⁻¹ := by
        rw [Finset.prod_inv_distrib]
      _ = (d : ℝ)⁻¹ := by
        have hpd : (∏ p ∈ d.primeFactors, p : ℕ) = d :=
          Nat.prod_primeFactors_of_squarefree hdinfo.1
        have hpdR : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
          simpa only [Nat.cast_prod] using congrArg (fun n : ℕ => (n : ℝ)) hpd
        exact congrArg (fun t : ℝ => t⁻¹) hpdR
  have hfilter :
      S.objects.filter (fun n => d ∣ n) =
        (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
          (fun n => n % r = a % r ∧ d ∣ n) := by
    ext n
    simp [S, SieveData.objects, apSieveData]
    tauto
  have hcount := apDivResidueCount_error ⌊lo⌋₊ ⌊hi⌋₊ r a d
    (by omega) hdpos hcoprd (Nat.floor_mono hlohi)
  have hfloor :
      |((⌊hi⌋₊ : ℝ) - ⌊lo⌋₊) - (hi - lo)| ≤ 2 := by
    have hfl₁ : (⌊lo⌋₊ : ℝ) ≤ lo := Nat.floor_le (by linarith)
    have hfl₂ : (⌊hi⌋₊ : ℝ) ≤ hi := Nat.floor_le (by linarith)
    have hfu₁ : lo < (⌊lo⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one lo
    have hfu₂ : hi < (⌊hi⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one hi
    rw [abs_le]
    constructor <;> linarith
  have hden : (1 : ℝ) ≤ (r : ℝ) * d := by
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hdbound
    nlinarith
  have hscaled :
      |(((⌊hi⌋₊ : ℝ) - ⌊lo⌋₊) / ((r : ℝ) * d)) -
        (hi - lo) / ((r : ℝ) * d)| ≤ 2 := by
    rw [← sub_div, abs_div]
    calc
      |(⌊hi⌋₊ : ℝ) - ⌊lo⌋₊ - (hi - lo)| / |(r : ℝ) * d| ≤
          2 / |(r : ℝ) * d| := div_le_div_of_nonneg_right hfloor (abs_nonneg _)
      _ ≤ 2 := by
        have hdenabs : (1 : ℝ) ≤ |(r : ℝ) * d| := by
          rw [abs_of_pos (by positivity)]
          exact hden
        apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hdenabs)).2
        nlinarith
  have hmain : X * (d : ℝ)⁻¹ = (hi - lo) / ((r : ℝ) * d) := by
    dsimp [X]
    field_simp
  have hrem : S.remainder d =
      (((S.objects.filter (fun n => d ∣ n)).card : ℝ) -
        (hi - lo) / ((r : ℝ) * d)) := by
    unfold SieveData.remainder
    rw [hsum, hprod]
    simp only [S, apSieveData]
    rw [hmain]
  have hcount' :
      |(((S.objects.filter (fun n => d ∣ n)).card : ℝ) -
        ((⌊hi⌋₊ : ℝ) - ⌊lo⌋₊) / ((r : ℝ) * d))| ≤ 2 := by
    rw [hfilter]
    simpa only [Nat.cast_mul] using hcount
  rw [hrem]
  calc
    |((S.objects.filter (fun n => d ∣ n)).card : ℝ) -
        (hi - lo) / ((r : ℝ) * d)| =
      |((((S.objects.filter (fun n => d ∣ n)).card : ℝ) -
        ((⌊hi⌋₊ : ℝ) - ⌊lo⌋₊) / ((r : ℝ) * d)) +
        (((⌊hi⌋₊ : ℝ) - ⌊lo⌋₊) / ((r : ℝ) * d) -
          (hi - lo) / ((r : ℝ) * d)))| := by ring_nf
    _ ≤ |((S.objects.filter (fun n => d ∣ n)).card : ℝ) -
          ((⌊hi⌋₊ : ℝ) - ⌊lo⌋₊) / ((r : ℝ) * d)| +
        |((⌊hi⌋₊ : ℝ) - ⌊lo⌋₊) / ((r : ℝ) * d) -
          (hi - lo) / ((r : ℝ) * d)| := abs_add_le _ _
    _ ≤ 4 := by linarith [hcount', hscaled]

def reciprocalPrimeSum (y : ℝ) : ℝ :=
  Finset.sum (primesUpTo y) (fun p : ℕ => (p : ℝ)⁻¹)

lemma reciprocalPrimeSum_shell (w : ℝ) (hw : 1 < w) :
    Finset.sum ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ)))
      (fun p : ℕ => (p : ℝ)⁻¹) = reciprocalPrimeSum (w ^ 2) - reciprocalPrimeSum w := by
  have hw2 : w ≤ w ^ 2 := by nlinarith [sq_nonneg (w - 1)]
  let P : Finset ℕ := primesUpTo (w ^ 2)
  let Q : Finset ℕ := primesUpTo w
  have hsub : Q ⊆ P := by
    intro p hp
    apply mem_primesUpTo.mpr
    rcases mem_primesUpTo.mp hp with ⟨hpp, hpw⟩
    exact ⟨hpp, hpw.trans hw2⟩
  have hsmall : P.filter (fun p : ℕ => (p : ℝ) ≤ w) = Q := by
    ext p
    simp only [Finset.mem_filter]
    change (p ∈ primesUpTo (w ^ 2) ∧ (p : ℝ) ≤ w) ↔ p ∈ primesUpTo w
    rw [mem_primesUpTo, mem_primesUpTo]
    constructor
    · rintro ⟨⟨hpp, _⟩, hpw⟩
      exact ⟨hpp, hpw⟩
    · rintro ⟨hpp, hpw⟩
      exact ⟨⟨hpp, hpw.trans hw2⟩, hpw⟩
  have hlarge : P.filter (fun p : ℕ => w < (p : ℝ)) =
      P.filter (fun p : ℕ => ¬ (p : ℝ) ≤ w) := by
    ext p
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => lt_iff_not_ge
  let f : ℕ → ℝ := fun p => (p : ℝ)⁻¹
  have hsplit' :
      Finset.sum Q f + Finset.sum (P.filter (fun p : ℕ => w < (p : ℝ))) f =
        Finset.sum P f := by
    rw [← hsmall, hlarge]
    exact Finset.sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) ≤ w) f
  have hrec :
      reciprocalPrimeSum (w ^ 2) - reciprocalPrimeSum w =
        Finset.sum (P.filter (fun p : ℕ => w < (p : ℝ))) f := by
    dsimp [reciprocalPrimeSum, P, Q, f]
    linarith [hsplit']
  exact hrec.symm

lemma apSieve_density_bounds (K : ℝ)
    (hM : ∀ y : ℝ, 2 ≤ y →
      |reciprocalPrimeSum y - Real.log (Real.log y)| ≤ K)
    (hK : 0 ≤ K) (z X lo hi : ℝ) (r a : ℕ)
    (hX : 0 ≤ X) (hz : 1 < z) :
    0 < 2 * K + 10 ∧
      (apSieveData z X lo hi r a hX).densityBounds z (1 / 2) (2 * K + 10) := by
  let C : ℝ := 2 * K + 10
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨hC, hz, by norm_num, ?_, ?_⟩
  · intro p hp
    rcases apSieve_prime_not_dvd hp with ⟨hpp, hpz, _⟩
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      have hinv := (inv_le_inv₀ hppos (by norm_num : (0 : ℝ) < 2)).2 hp2
      norm_num at hinv
      nlinarith
    have hnonneg : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hppos.le
    have hupper : (p : ℝ)⁻¹ ≤ 1 - 1 / 2 := by norm_num; linarith
    exact ⟨hpz, hnonneg, hupper⟩
  · intro w hw
    let shellS : Finset ℕ := (apSievePrimes z r).filter
      (fun p => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ 2)
    change Finset.sum shellS (fun p : ℕ => (p : ℝ)⁻¹) ≤ C
    let smallPrimes : Finset ℕ := Finset.Icc 1 3
    have hsubset (hsmall : w < 2) : shellS ⊆ smallPrimes := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, ⟨_, hpw2⟩⟩
      rcases apSieve_prime_not_dvd hpS with ⟨hpp, _, _⟩
      have hp2 : 2 ≤ p := hpp.two_le
      have hp1 : 1 ≤ p := by omega
      have hp3r : (p : ℝ) < 4 := by nlinarith
      have hp3nat : p < 4 := by exact_mod_cast hp3r
      have hp3 : p ≤ 3 := by omega
      exact Finset.mem_Icc.mpr ⟨hp1, hp3⟩
    by_cases hsmall : w < 2
    · have hsum₁ :
          Finset.sum shellS (fun p : ℕ => (p : ℝ)⁻¹) ≤
            Finset.sum smallPrimes (fun p : ℕ => (p : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg (hsubset hsmall)
          (by intro p hp hpn; positivity)
      have hsum₂ :
          Finset.sum smallPrimes (fun p : ℕ => (p : ℝ)⁻¹) ≤
            Finset.sum smallPrimes (fun _ : ℕ => (1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hp).1
        have hpPos : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp1)
        have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp1
        rw [inv_le_one₀ hpPos]
        exact hp1r
      have hcard : Finset.sum smallPrimes (fun _ : ℕ => (1 : ℝ)) = 3 := by
        simp [smallPrimes]
      -- The small-w case is bounded directly by the three possible integers.
      have hsimp :
          Finset.sum shellS (fun p : ℕ => (p : ℝ)⁻¹) ≤ 3 :=
        hsum₁.trans (hsum₂.trans_eq hcard)
      have hC3 : (3 : ℝ) ≤ C := by dsimp [C]; linarith
      exact le_trans hsimp hC3
    · have hw2 : 2 ≤ w := le_of_not_gt hsmall
      have hsumS :
          Finset.sum shellS (fun p : ℕ => (p : ℝ)⁻¹) ≤
            Finset.sum ((primesUpTo (w ^ 2)).filter (fun p : ℕ => w < (p : ℝ)))
              (fun p : ℕ => (p : ℝ)⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpS, ⟨hpw, hpw2⟩⟩
          rcases apSieve_prime_not_dvd hpS with ⟨hpp, _, _⟩
          exact Finset.mem_filter.mpr ⟨mem_primesUpTo.mpr ⟨hpp, hpw2⟩, hpw⟩
        · intro p hp hpn
          positivity
      rw [reciprocalPrimeSum_shell w hw] at hsumS
      have hmw := hM w hw2
      have hmw2 := hM (w ^ 2) (by nlinarith [hw2])
      rw [abs_le] at hmw hmw2
      have hlog : Real.log (Real.log (w ^ 2)) - Real.log (Real.log w) = Real.log 2 := by
        have hwlog : Real.log (w ^ 2) = 2 * Real.log w := by
          rw [Real.log_pow]
          norm_num
        rw [hwlog, Real.log_mul (by norm_num) (ne_of_gt (Real.log_pos hw))]
        ring
      have hlog2 : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      unfold reciprocalPrimeSum at hsumS hmw hmw2
      have hshell :
          (∑ p ∈ shellS, (p : ℝ)⁻¹) ≤ 2 * K + 1 := by
        linarith [hsumS, hmw.1, hmw2.2, hlog, hlog2]
      dsimp [C]
      linarith [hshell]

lemma apSieve_rough_iff {z : ℝ} {r a n : ℕ} (hn : 0 < n)
    (hcop : Nat.Coprime a r) (hres : n % r = a % r)
    (hpr : ∀ p : ℕ, p.Prime → p ∣ r → (p : ℝ) ≤ z) :
    rough z n ↔ ∀ p ∈ apSievePrimes z r, ¬ p ∣ n := by
  have hcopnr : Nat.Coprime n r := by
    have hmodcop : (n % r).Coprime r := by
      rw [hres]
      exact (ZMod.coprime_mod_iff_coprime a r).2 hcop
    exact (ZMod.coprime_mod_iff_coprime n r).1 hmodcop
  constructor
  · intro hrough p hp hpn
    rcases apSieve_prime_not_dvd hp with ⟨hpp, hpz, _⟩
    have hlarge := hrough.2 p hpp hpn
    exact (not_le_of_gt hlarge) hpz
  · intro hrough
    refine ⟨hn, ?_⟩
    intro p hpp hpn
    by_contra hpnot
    have hpz : (p : ℝ) ≤ z := le_of_not_gt hpnot
    by_cases hprdiv : p ∣ r
    · have hdivgcd : p ∣ Nat.gcd n r := Nat.dvd_gcd hpn hprdiv
      rw [Nat.coprime_iff_gcd_eq_one.mp hcopnr] at hdivgcd
      have hple : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdivgcd
      have hp2 : 2 ≤ p := hpp.two_le
      omega
    · have hmem : p ∈ apSievePrimes z r := by
        apply Finset.mem_filter.mpr
        exact ⟨mem_primesUpTo.mpr ⟨hpp, hpz⟩, hprdiv⟩
      exact (hrough p hmem) hpn

lemma apSieve_sifted_count (z lo hi : ℝ) (r a : ℕ)
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hr : 0 < r)
    (hcop : Nat.Coprime a r)
    (hpr : ∀ p : ℕ, p.Prime → p ∣ r → (p : ℝ) ≤ z) :
    (apSieveData z ((hi - lo) / r) lo hi r a
      (div_nonneg (sub_nonneg.mpr hlohi) (by positivity))).sifted =
      ((Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
        (fun n => rough z n ∧ n % r = a % r)).card := by
  let X : ℝ := (hi - lo) / r
  have hX : 0 ≤ X := by dsimp [X]; positivity
  let S : SieveData ℕ := apSieveData z X lo hi r a hX
  have hrough {n : ℕ} (hn : n ∈ S.objects) :
      (∀ p ∈ S.primes, ¬ S.bad p n) ↔ rough z n := by
    rcases Finset.mem_filter.mp hn with ⟨_, hres⟩
    exact (apSieve_rough_iff (by
      have hloN : (1 : ℕ) ≤ ⌊lo⌋₊ :=
        (Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).mpr (by simpa using hlo)
      have : ⌊lo⌋₊ < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
      omega) hcop hres hpr).symm
  have hsum :
      S.sifted =
        ((S.objects.filter (fun n => rough z n)).card : ℝ) := by
    unfold SieveData.sifted
    calc
      (∑ n ∈ S.objects, if ∀ p ∈ S.primes, ¬ S.bad p n then S.weight n else 0) =
          ∑ n ∈ S.objects, if rough z n then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hiff := hrough hn
        have hiff' :
            (∀ p ∈ apSievePrimes z r, ¬ p ∣ n) ↔ rough z n := by
          simpa [S, apSieveData, SieveData.bad] using hiff
        simpa [S, SieveData.weight, apSieveData, SieveData.bad, hiff']
      _ = ((S.objects.filter (fun n => rough z n)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp
  have hfilter :
      S.objects.filter (fun n => rough z n) =
        (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
          (fun n => rough z n ∧ n % r = a % r) := by
    ext n
    simp [S, SieveData.objects, apSieveData, and_comm]
    tauto
  rw [show (apSieveData z ((hi - lo) / r) lo hi r a
      (div_nonneg (sub_nonneg.mpr hlohi) (by positivity))).sifted = S.sifted by rfl]
  rw [hsum, hfilter]

lemma apSieve_product_totient (z : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hpr : ∀ p : ℕ, p.Prime → p ∣ r → (p : ℝ) ≤ z) :
    Finset.prod (apSievePrimes z r) (fun p : ℕ => 1 - (p : ℝ)⁻¹) =
      sieveProduct z * (r : ℝ) / (Nat.totient r : ℝ) := by
  have hr0 : r ≠ 0 := by omega
  let E : ℝ := Finset.prod r.primeFactors (fun p : ℕ => 1 - (p : ℝ)⁻¹)
  let Q : ℝ := Finset.prod (apSievePrimes z r) (fun p : ℕ => 1 - (p : ℝ)⁻¹)
  have hcommon : (primesUpTo z).filter (fun p => p ∣ r) = r.primeFactors := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpz, hprdiv⟩
      exact Nat.Prime.mem_primeFactors (mem_primesUpTo.mp hpz).1 hprdiv hr0
    · intro hp
      rcases Nat.mem_primeFactors.mp hp with ⟨hpp, hprdiv, _⟩
      exact Finset.mem_filter.mpr ⟨mem_primesUpTo.mpr ⟨hpp, hpr p hpp hprdiv⟩, hprdiv⟩
  have hsplit :
      Finset.prod ((primesUpTo z).filter (fun p : ℕ => p ∣ r))
          (fun p : ℕ => 1 - (p : ℝ)⁻¹) *
        Finset.prod ((primesUpTo z).filter (fun p : ℕ => ¬ p ∣ r))
          (fun p : ℕ => 1 - (p : ℝ)⁻¹) = sieveProduct z := by
    simpa [sieveProduct] using
      (Finset.prod_filter_mul_prod_filter_not (primesUpTo z)
        (fun p : ℕ => p ∣ r) (fun p : ℕ => 1 - (p : ℝ)⁻¹))
  have hdecomp : E * Q = sieveProduct z := by
    simpa [E, Q, apSievePrimes, hcommon] using hsplit
  have hphiQ := Nat.totient_eq_mul_prod_factors r
  have hphiCast := congrArg (Rat.castHom ℝ) hphiQ
  have hphi : (Nat.totient r : ℝ) = (r : ℝ) * E := by
    simpa [E, Rat.cast_prod] using hphiCast
  have hEpos : 0 < E := by
    apply Finset.prod_pos
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have h := (inv_le_inv₀ hppos (by norm_num : (0 : ℝ) < 2)).2 hp2
      norm_num at h
      exact h
    linarith
  have hEr : E ≠ 0 := ne_of_gt hEpos
  have hrr : (r : ℝ) ≠ 0 := by positivity
  have hsolve : Q = E⁻¹ * sieveProduct z := by
    calc
      Q = (E * Q) / E := by field_simp [hEr]
      _ = sieveProduct z / E := by rw [hdecomp]
      _ = E⁻¹ * sieveProduct z := by ring
  calc
    Finset.prod (apSievePrimes z r) (fun p : ℕ => 1 - (p : ℝ)⁻¹) = Q := rfl
    _ = E⁻¹ * sieveProduct z := hsolve
    _ = sieveProduct z * (r : ℝ) / (Nat.totient r : ℝ) := by
      rw [hphi]
      field_simp [hrr, hEr]

lemma apSieve_remainderSum_bound (z lo hi : ℝ) (r a : ℕ)
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hr : 1 ≤ r) (D : ℝ) (hD : 1 ≤ D) :
    (apSieveData z ((hi - lo) / r) lo hi r a
      (div_nonneg (sub_nonneg.mpr hlohi) (by positivity))).remainderSum D ≤ 4 * (D + 1) := by
  let X : ℝ := (hi - lo) / r
  have hX : 0 ≤ X := by dsimp [X]; positivity
  let S : SieveData ℕ := apSieveData z X lo hi r a hX
  have hcard : (S.products D).card ≤ ⌊D⌋₊ + 1 := by
    have hsub : S.products D ⊆ Finset.Icc 0 ⌊D⌋₊ := by
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).1
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hd').2⟩
    calc
      (S.products D).card ≤ (Finset.Icc 0 ⌊D⌋₊).card := Finset.card_le_card hsub
      _ = ⌊D⌋₊ + 1 := by simp
  have hcardReal : ((S.products D).card : ℝ) ≤ D + 1 := by
    have hcast : ((S.products D).card : ℝ) ≤ (⌊D⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
    have hfloor : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le (by linarith)
    linarith
  have hsum :
      (∑ d ∈ S.products D, |S.remainder d|) ≤
        ∑ _d ∈ S.products D, (4 : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    exact apSieve_remainder_error z lo hi r a hlo hlohi hr D hd
  have hsum' : S.remainderSum D ≤ 4 * (S.products D).card := by
    unfold SieveData.remainderSum
    calc
      (∑ d ∈ S.products D, |S.remainder d|) ≤
          ∑ _d ∈ S.products D, (4 : ℝ) := hsum
      _ = 4 * (S.products D).card := by simp [mul_comm]
  have hmain : S.remainderSum D ≤ 4 * (D + 1) := by
    calc
      S.remainderSum D ≤ 4 * (S.products D).card := hsum'
      _ ≤ 4 * (D + 1) := by nlinarith [hcardReal]
  simpa [S, X, SieveData.remainderSum, apSieveData] using hmain

lemma log_div_sqrt_tendsto_zero :
    Tendsto (fun t : ℝ => Real.log t / Real.sqrt t) atTop (nhds 0) := by
  have hsmall : (fun t : ℝ => Real.log (Real.sqrt t)) =o[atTop]
      (fun t : ℝ => Real.sqrt t) :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_sqrt_atTop
  have hquot := hsmall.tendsto_div_nhds_zero
  have hmul : Tendsto (fun t : ℝ => 2 * (Real.log (Real.sqrt t) / Real.sqrt t))
      atTop (nhds 0) := by simpa using tendsto_const_nhds.mul hquot
  have heq : (fun t : ℝ => Real.log t / Real.sqrt t) =ᶠ[atTop]
      fun t => 2 * (Real.log (Real.sqrt t) / Real.sqrt t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.log_sqrt ht.le]
    ring
  exact hmul.congr' heq.symm

lemma eventually_rpow_lt_exp_sqrt (B : ℝ) (hB : 0 < B) :
    ∀ᶠ t : ℝ in atTop, 1 < t ∧ t ^ B < Real.exp (Real.sqrt t) := by
  have hratio := log_div_sqrt_tendsto_zero
  have heps : ∀ᶠ t : ℝ in atTop, Real.log t / Real.sqrt t < 1 / (B + 1) :=
    hratio.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [eventually_gt_atTop (1 : ℝ), heps] with t ht hratio'
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 (by linarith)
  have hratioInv : Real.log t / Real.sqrt t < (B + 1)⁻¹ := by
    simpa [one_div] using hratio'
  have hfrac : B * (Real.log t / Real.sqrt t) < 1 := by
    calc
      B * (Real.log t / Real.sqrt t) < B * (B + 1)⁻¹ :=
        mul_lt_mul_of_pos_left hratioInv hB
      _ < 1 := (div_lt_one₀ (by linarith)).2 (by nlinarith)
  have hlog : B * Real.log t < Real.sqrt t := by
    have hfrac' : (B * Real.log t) / Real.sqrt t < 1 := by
      convert hfrac using 1 <;> ring
    simpa using (div_lt_iff₀ hsqrt).mp hfrac'
  have hpow : t ^ B = Real.exp (Real.log t * B) :=
    Real.rpow_def_of_pos (by linarith) B
  refine ⟨ht, ?_⟩
  rw [hpow]
  exact Real.exp_lt_exp.mpr (by nlinarith)

lemma sieveProduct_pos (z : ℝ) : 0 < sieveProduct z := by
  unfold sieveProduct
  apply Finset.prod_pos
  intro p hp
  have hpp : p.Prime := (mem_primesUpTo.mp hp).1
  have hp2 : 2 ≤ p := hpp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hpPos : (0 : ℝ) < p := by linarith
  have hinv : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpPos).2 hp1
  linarith

theorem RoughResidueIntervalTask_proof : RoughResidueIntervalTask := by
  intro hc hs b C B A eta hb hC hB hA heta
  obtain ⟨Km, hMraw⟩ := hc.mertens.1
  have hKm : 0 ≤ Km := by
    have hM2 := hMraw 2 (by norm_num)
    exact le_trans (abs_nonneg _) hM2
  have hM : ∀ y : ℝ, 2 ≤ y →
      |reciprocalPrimeSum y - Real.log (Real.log y)| ≤ Km := by
    simpa [reciprocalPrimeSum] using hMraw
  let Cs : ℝ := 2 * Km + 10
  have hCs : 0 < Cs := by dsimp [Cs]; linarith
  obtain ⟨K, hK, h₀, hBlock⟩ := hs.block (1 / 2) Cs (by norm_num) hCs
  let c : ℝ := A + |Real.log K| + 1
  have hcpos : 0 < c := by dsimp [c]; positivity
  let H : ℝ → ℕ := fun t => 2 * Nat.ceil (c * Real.log t)
  have hH₀ : ∀ᶠ t : ℝ in atTop, h₀ ≤ H t := by
    have hlogLarge : ∀ᶠ t : ℝ in atTop, (h₀ : ℝ) / c ≤ Real.log t :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((h₀ : ℝ) / c))
    filter_upwards [hlogLarge] with t ht
    have hceil : c * Real.log t ≤ (Nat.ceil (c * Real.log t) : ℝ) := Nat.le_ceil _
    have hHcast : (H t : ℝ) = 2 * (Nat.ceil (c * Real.log t) : ℝ) := by simp [H]
    have hreal : (h₀ : ℝ) ≤ (H t : ℝ) := by
      rw [hHcast]
      have hmul : (h₀ : ℝ) ≤ c * Real.log t := by
        have hmul' := (div_le_iff₀ hcpos).mp ht
        nlinarith
      have hnonneg : 0 ≤ (Nat.ceil (c * Real.log t) : ℝ) := Nat.cast_nonneg _
      have hsmall : (h₀ : ℝ) ≤ (Nat.ceil (c * Real.log t) : ℝ) := hmul.trans hceil
      nlinarith [hsmall, hnonneg]
    exact_mod_cast hreal
  have hlogratio := log_div_sqrt_tendsto_zero
  have hinvsqrt : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hratioLimit :
      Tendsto (fun t : ℝ => 8 * c * (Real.log t / Real.sqrt t) +
        10 * (Real.sqrt t)⁻¹) atTop (nhds 0) := by
    have h₁ : Tendsto (fun t : ℝ => 8 * c * (Real.log t / Real.sqrt t))
        atTop (nhds 0) := by simpa using (tendsto_const_nhds.mul hlogratio)
    have h₂ : Tendsto (fun t : ℝ => 10 * (Real.sqrt t)⁻¹)
        atTop (nhds 0) := by simpa using (tendsto_const_nhds.mul hinvsqrt)
    simpa using h₁.add h₂
  have hratioSmall : ∀ᶠ t : ℝ in atTop,
      8 * c * (Real.log t / Real.sqrt t) + 10 * (Real.sqrt t)⁻¹ < eta / 2 :=
    hratioLimit.eventually (Iio_mem_nhds (by positivity))
  have hLevelBound : ∀ᶠ t : ℝ in atTop,
      ((4 * H t + 2 : ℕ) : ℝ) * Real.sqrt t ≤ eta / 2 * t := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hratioSmall] with t ht hratio
    have htpos : 0 < t := by linarith
    have hspos : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
    have hsq : Real.sqrt t * Real.sqrt t = t := by
      simpa [pow_two] using Real.sq_sqrt (by linarith : 0 ≤ t)
    have hceil0 : 0 ≤ c * Real.log t :=
      mul_nonneg hcpos.le (Real.log_pos ht).le
    have hceilUpper : (Nat.ceil (c * Real.log t) : ℝ) ≤ c * Real.log t + 1 :=
      (Nat.ceil_lt_add_one hceil0).le
    have hHcast : (H t : ℝ) = 2 * (Nat.ceil (c * Real.log t) : ℝ) := by simp [H]
    have hlevelCast : ((4 * H t + 2 : ℕ) : ℝ) = 4 * (H t : ℝ) + 2 := by
      norm_num [Nat.cast_add, Nat.cast_mul]
    have hlevelNat : ((4 * H t + 2 : ℕ) : ℝ) ≤ 8 * c * Real.log t + 10 := by
      rw [hlevelCast, hHcast]
      nlinarith
    have hscaleEq : (8 * c * Real.log t + 10) * Real.sqrt t =
        t * (8 * c * (Real.log t / Real.sqrt t) + 10 * (Real.sqrt t)⁻¹) := by
      have htne : t ≠ 0 := ne_of_gt htpos
      have hsne : Real.sqrt t ≠ 0 := hspos.ne'
      field_simp [htne, hsne]
      nlinarith [hsq]
    calc
      ((4 * H t + 2 : ℕ) : ℝ) * Real.sqrt t ≤
          (8 * c * Real.log t + 10) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right hlevelNat (Real.sqrt_nonneg _)
      _ = t * (8 * c * (Real.log t / Real.sqrt t) + 10 * (Real.sqrt t)⁻¹) := hscaleEq
      _ ≤ t * (eta / 2) := mul_le_mul_of_nonneg_left hratio.le (by linarith)
      _ = eta / 2 * t := by ring
  have hlinear : Tendsto (fun t : ℝ => (eta / 2) * t) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity : 0 < eta / 2)).2 tendsto_id
  have hconstExp : ∀ᶠ t : ℝ in atTop, 8 * K ≤ Real.exp (eta / 2 * t) :=
    (Real.tendsto_exp_atTop.comp hlinear).eventually (eventually_ge_atTop (8 * K))
  have hpowBound : ∀ᶠ t : ℝ in atTop, t ^ B < Real.exp (Real.sqrt t) := by
    filter_upwards [eventually_rpow_lt_exp_sqrt B hB] with t ht
    exact ht.2
  have hbase : ∀ᶠ t : ℝ in atTop, Real.exp 1 ≤ t :=
    eventually_ge_atTop (Real.exp 1)
  let GoodT : ℝ → Prop := fun t => Real.exp 1 ≤ t ∧ h₀ ≤ H t ∧
        ((4 * H t + 2 : ℕ) : ℝ) * Real.sqrt t ≤ eta / 2 * t ∧
        8 * K ≤ Real.exp (eta / 2 * t) ∧ t ^ B < Real.exp (Real.sqrt t)
  have hgoodT : ∀ᶠ t : ℝ in atTop, GoodT t := by
    filter_upwards [hbase, hH₀, hLevelBound, hconstExp, hpowBound]
      with t h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hgoodX : ∀ᶠ x : ℝ in atTop, GoodT (Real.log x) :=
    Real.tendsto_log_atTop.eventually hgoodT
  filter_upwards [eventually_gt_atTop (1 : ℝ), hgoodX] with x hx hgood
  let t : ℝ := Real.log x
  let h : ℕ := H t
  let z : ℝ := Real.exp (Real.sqrt t)
  have htbase : Real.exp 1 ≤ t := by simpa [t] using hgood.1
  have htpos : 0 < t := by have := Real.exp_pos 1; linarith
  have ht1 : 1 < t := by have := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1); linarith
  have hhle : h₀ ≤ h := by simpa [h, t] using hgood.2.1
  have hlevel : ((4 * h + 2 : ℕ) : ℝ) * Real.sqrt t ≤ eta / 2 * t := by
    simpa [h, t] using hgood.2.2.1
  have hconst : 8 * K ≤ Real.exp (eta / 2 * t) := by simpa [t] using hgood.2.2.2.1
  have hmod : t ^ B < z := by simpa [z, t] using hgood.2.2.2.2
  have hz : 1 < z := by dsimp [z]; exact Real.one_lt_exp_iff.mpr (Real.sqrt_pos.2 htpos)
  have hEven : Even h := by
    refine ⟨Nat.ceil (c * Real.log t), ?_⟩
    simp [h, H, two_mul]
  have hcoeff : K * Real.exp (-(h : ℝ)) ≤ t ^ (-A) := by
    have htlog : 1 ≤ Real.log t := by
      have hh := Real.log_le_log (Real.exp_pos 1) htbase
      simpa using hh
    have hceil : c * Real.log t ≤ (Nat.ceil (c * Real.log t) : ℝ) := Nat.le_ceil _
    have hHcast : (h : ℝ) = 2 * (Nat.ceil (c * Real.log t) : ℝ) := by simp [h, H]
    have hlogK : Real.log K ≤ |Real.log K| := le_abs_self _
    have hcoeffLog : Real.log K - (h : ℝ) ≤ -A * Real.log t := by
      rw [hHcast]
      dsimp [c] at hceil ⊢
      have hAlog : 0 ≤ A * Real.log t := mul_nonneg hA.le (by linarith)
      have hAbLog : 0 ≤ |Real.log K| * (Real.log t - 1) :=
        mul_nonneg (abs_nonneg _) (sub_nonneg.mpr htlog)
      nlinarith [hceil, hlogK, hAlog, hAbLog]
    have hKexp : K = Real.exp (Real.log K) := (Real.exp_log hK).symm
    have hprodExp : K * Real.exp (-(h : ℝ)) =
        Real.exp (Real.log K - (h : ℝ)) := by
      calc
        K * Real.exp (-(h : ℝ)) = Real.exp (Real.log K) * Real.exp (-(h : ℝ)) :=
          congrArg (fun y : ℝ => y * Real.exp (-(h : ℝ))) hKexp
        _ = Real.exp (Real.log K + -(h : ℝ)) := by rw [← Real.exp_add]
        _ = _ := by congr 1 <;> ring
    have hpow : t ^ (-A) = Real.exp (-A * Real.log t) := by
      rw [Real.rpow_def_of_pos htpos (-A)]
      congr 1 <;> ring
    rw [hprodExp, hpow]
    exact Real.exp_le_exp.mpr hcoeffLog
  have hD : 1 ≤ z ^ (4 * h + 2) := by
    apply one_le_pow₀
    exact le_of_lt hz
  have hDexp : z ^ (4 * h + 2) ≤ Real.exp (eta / 2 * t) := by
    have hpow : z ^ (4 * h + 2) =
        Real.exp (Real.sqrt t * ((4 * h + 2 : ℕ) : ℝ)) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.exp_mul]
    rw [hpow]
    exact Real.exp_le_exp.mpr (by nlinarith [hlevel])
  have hDrem : 4 * K * (z ^ (4 * h + 2) + 1) ≤ x ^ eta := by
    have hDge : 1 ≤ z ^ (4 * h + 2) := hD
    have hDplus : z ^ (4 * h + 2) + 1 ≤ 2 * z ^ (4 * h + 2) := by linarith
    have hfirst : 4 * K * (z ^ (4 * h + 2) + 1) ≤
        8 * K * z ^ (4 * h + 2) := by
      calc
        4 * K * (z ^ (4 * h + 2) + 1) ≤
            4 * K * (2 * z ^ (4 * h + 2)) :=
          mul_le_mul_of_nonneg_left hDplus (by positivity : 0 ≤ 4 * K)
        _ = 8 * K * z ^ (4 * h + 2) := by ring
    have hsecond : 8 * K * z ^ (4 * h + 2) ≤
        Real.exp (eta / 2 * t) * Real.exp (eta / 2 * t) := by
      calc
        8 * K * z ^ (4 * h + 2) ≤ Real.exp (eta / 2 * t) * z ^ (4 * h + 2) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
        _ ≤ Real.exp (eta / 2 * t) * Real.exp (eta / 2 * t) :=
          mul_le_mul_of_nonneg_left hDexp (by positivity)
    have hexp : Real.exp (eta / 2 * t) * Real.exp (eta / 2 * t) =
        Real.exp (eta * t) := by rw [← Real.exp_add]; congr 1 <;> ring
    have hxpow : x ^ eta = Real.exp (eta * t) := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < x) eta]
      congr 1 <;> ring
    rw [hxpow, ← hexp]
    exact hfirst.trans hsecond
  intro lo hi r a hlo horder hhi hrNat hrBound hcop
  have hxpow : 1 < x ^ b := Real.one_lt_rpow hx hb
  have hlo1 : 1 ≤ lo := (le_of_lt hxpow).trans hlo
  have hrpos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hrNat
  have hrR : 1 ≤ (r : ℝ) := by exact_mod_cast hrNat
  have hrBoundT : (r : ℝ) ≤ t ^ B := by simpa [t, Analytic.L] using hrBound
  have hrLtZ : (r : ℝ) < z := lt_of_le_of_lt hrBoundT hmod
  have hprimeR : ∀ p : ℕ, p.Prime → p ∣ r → (p : ℝ) ≤ z := by
    intro p hp hpd
    have hr0 : r ≠ 0 := by omega
    have hpNat : p ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hpd
    have hpR : (p : ℝ) ≤ r := by exact_mod_cast hpNat
    exact hpR.trans hrLtZ.le
  let X : ℝ := (hi - lo) / r
  have hX : 0 ≤ X := by dsimp [X]; positivity
  let S : SieveData ℕ := apSieveData z X lo hi r a hX
  have hDen : S.densityBounds z (1 / 2) Cs := by
    have h := (apSieve_density_bounds Km hM hKm z X lo hi r a hX hz).2
    simpa [S, X, Cs, apSieveData] using h
  have hcount : S.sifted =
      ((Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
        (fun n => rough z n ∧ n % r = a % r)).card := by
    simpa [S, X, apSieveData] using
      apSieve_sifted_count z lo hi r a hlo1 horder hrpos hcop hprimeR
  have hprod : S.product = sieveProduct z * (r : ℝ) / (Nat.totient r : ℝ) := by
    simpa [S, SieveData.product, apSieveData] using
      apSieve_product_totient z r hrNat hprimeR
  have hrCastPos : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have hphiPos : 0 < (Nat.totient r : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hrpos)
  let M : ℝ := (hi - lo) * sieveProduct z / (Nat.totient r : ℝ)
  have hmain : S.X * S.product = M := by
    rw [show S.X = X by rfl, hprod]
    dsimp [M, X]
    field_simp [hrCastPos.ne', hphiPos.ne']
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr horder) (sieveProduct_pos z).le) hphiPos.le
  let D : ℝ := z ^ (4 * h + 2)
  have hD : 1 ≤ D := by simpa [D] using (show 1 ≤ z ^ (4 * h + 2) from one_le_pow₀ hz.le)
  have hrem : S.remainderSum D ≤ 4 * (D + 1) := by
    simpa [S, X, D, apSieveData] using
      apSieve_remainderSum_bound z lo hi r a hlo1 horder hrNat D hD
  have hblockData := hBlock ℕ S z hDen
  have hblockPair := (hblockData.2 h hhle hEven).1
  have hcountErr :
      |(((Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
          (fun n => rough z n ∧ n % r = a % r)).card : ℝ) - M| ≤
        K * Real.exp (-(h : ℝ)) * M + K * S.remainderSum D := by
    calc
      |(((Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
          (fun n => rough z n ∧ n % r = a % r)).card : ℝ) - M| =
          |S.sifted - S.X * S.product| := by rw [← hcount, ← hmain]
      _ ≤ K * Real.exp (-(h : ℝ)) * S.X * S.product + K * S.remainderSum D := hblockPair
      _ = K * Real.exp (-(h : ℝ)) * M + K * S.remainderSum D := by
        rw [← hmain]
        ring
  have hcoeffTerm : K * Real.exp (-(h : ℝ)) * M ≤ M * t ^ (-A) := by
    calc
      K * Real.exp (-(h : ℝ)) * M = (K * Real.exp (-(h : ℝ))) * M := by ring
      _ ≤ t ^ (-A) * M := mul_le_mul_of_nonneg_right hcoeff hMnonneg
      _ = M * t ^ (-A) := by ring
  have hremTerm : K * S.remainderSum D ≤ x ^ eta := by
    calc
      K * S.remainderSum D ≤ K * (4 * (D + 1)) :=
        mul_le_mul_of_nonneg_left hrem hK.le
      _ = 4 * K * (D + 1) := by ring
      _ ≤ x ^ eta := hDrem
  have hfinal :
      |(((Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
          (fun n => rough z n ∧ n % r = a % r)).card : ℝ) - M| ≤
        M * t ^ (-A) + x ^ eta := by
    calc
      _ ≤ K * Real.exp (-(h : ℝ)) * M + K * S.remainderSum D := hcountErr
      _ ≤ M * t ^ (-A) + x ^ eta := add_le_add hcoeffTerm hremTerm
  exact hfinal

end Erdos821.P8Res

