import Erdos821.Blueprint.Proxy

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core.SieveBasics
open Blueprint Blueprint.Analytic

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

end Erdos821.P8Core.SieveBasics

