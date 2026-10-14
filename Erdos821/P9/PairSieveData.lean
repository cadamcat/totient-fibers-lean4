import Erdos821.P9.PairRemainder
import Erdos821.P9.PairEulerProduct
import Erdos821.Blueprint.Sieve
import Erdos821.Blueprint.Classical

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The fixed assignment progression for a pair of factors. -/
def pairSieveBaseGood (D d : ℕ) (z : ℕ × ℕ) : Prop :=
  pairBaseReduction D d (z.1 : ZMod (D * d)) *
      pairBaseReduction D d (z.2 : ZMod (D * d)) = 1

/-- The two local product bad events, evaluated on natural pairs. -/
def pairSieveBad (W : ℝ) (P A : Finset ℕ) (p : ℕ) (z : ℕ × ℕ) : Prop :=
  pairBadLocal p (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))
    ((z.1 : ZMod p), (z.2 : ZMod p))

theorem pairBaseReduction_natCast (D d n : ℕ) :
    pairBaseReduction D d (n : ZMod (D * d)) = (n : ZMod D) := by
  simp [pairBaseReduction]

theorem pairPrimeReduction_natCast (D d : ℕ) (p : d.primeFactors) (n : ℕ) :
    pairPrimeReduction D d p (n : ZMod (D * d)) = (n : ZMod p.val) := by
  simp [pairPrimeReduction]

theorem pairSieveBaseGood_eq_crtBase (D d : ℕ) (z : ℕ × ℕ) :
    pairSieveBaseGood D 1 z =
      (pairBaseReduction D d (z.1 : ZMod (D * d)) *
        pairBaseReduction D d (z.2 : ZMod (D * d)) = 1) := by
  simp [pairSieveBaseGood, pairBaseReduction_natCast]

theorem pairSieveBad_eq_crtLocal
    (D d : ℕ) (W : ℝ) (P A : Finset ℕ) (p : d.primeFactors) (z : ℕ × ℕ) :
    pairSieveBad W P A p.val z =
      pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A))
        (pairPrimeReduction D d p (z.1 : ZMod (D * d)),
          pairPrimeReduction D d p (z.2 : ZMod (D * d))) := by
  simp [pairSieveBad, pairPrimeReduction_natCast]

/-- Sieve data for pairs in a rectangular box on the fixed `D` progression. -/
def pairSieveData
    (a b c e D : ℕ) (W : ℝ) (P A Q : Finset ℕ)
    (hD : 0 < D)
    (hQprime : ∀ p ∈ Q, p.Prime) :
    Erdos821.Blueprint.SieveData (ℕ × ℕ) where
  objects := (Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
    (pairSieveBaseGood D 1)
  weight := fun _ => 1
  primes := Q
  bad := pairSieveBad W P A
  X := ((Nat.totient D : ℝ) * (b - a : ℕ) * (e - c : ℕ)) / (D : ℝ) ^ 2
  density := fun p => pairDensity p (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))
  nonneg := by intro z hz; norm_num
  prime := hQprime
  X_nonneg := by positivity


theorem sieveRemainder_eq_filtered_card
    {α : Type} (S : Erdos821.Blueprint.SieveData α) (d : ℕ)
    (hweight : ∀ a ∈ S.objects, S.weight a = 1) :
    S.remainder d =
      ((S.objects.filter fun a => ∀ p ∈ d.primeFactors, S.bad p a).card : ℝ) -
        S.X * S.g d := by
  classical
  rw [Erdos821.Blueprint.SieveData.remainder]
  have hcard : (S.objects.filter fun a => ∀ p ∈ d.primeFactors, S.bad p a).card =
      ∑ a ∈ S.objects, if ∀ p ∈ d.primeFactors, S.bad p a then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp [Finset.sum_filter]
  have hcardR : ((S.objects.filter fun a =>
      ∀ p ∈ d.primeFactors, S.bad p a).card : ℝ) =
      ∑ a ∈ S.objects, if ∀ p ∈ d.primeFactors, S.bad p a then 1 else 0 := by
    exact_mod_cast hcard
  rw [hcardR]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [hweight a ha]
  simp [Erdos821.Blueprint.SieveData.monomial]


theorem pairSieveData_local_filter_eq_crtRoots
    (a b c e D d : ℕ) (W : ℝ) (P A Q : Finset ℕ)
    (hD : 0 < D) (hQprime : ∀ p ∈ Q, p.Prime)
    [NeZero (D * d)] :
    let S := pairSieveData a b c e D W P A Q hD hQprime
    (S.objects.filter fun z =>
      ∀ p ∈ d.primeFactors, S.bad p z) =
      (Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter fun z =>
        pairResidue (D * d) z ∈
          (Finset.univ.filter fun v : ZMod (D * d) × ZMod (D * d) =>
            pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧
              ∀ p : d.primeFactors,
                pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
                  (decide (p.val ∉ P ∨ p.val ∉ A))
                  (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)) := by
  classical
  let S := pairSieveData a b c e D W P A Q hD hQprime
  let R : Finset (ZMod (D * d) × ZMod (D * d)) := Finset.univ.filter fun v =>
    pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧
      ∀ p : d.primeFactors,
        pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A))
          (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)
  ext z
  simp [pairSieveData, R, pairSieveBaseGood, pairSieveBad,
    pairBaseReduction_natCast, pairPrimeReduction_natCast, pairResidue]
  constructor
  · rintro ⟨⟨hz, hbase⟩, hbad⟩
    exact ⟨hz, ⟨hbase, hbad⟩⟩
  · rintro ⟨hz, ⟨hbase, hbad⟩⟩
    exact ⟨⟨hz, hbase⟩, hbad⟩



theorem pairSieveData_remainder_bound
    (a b c e D d : ℕ) (W : ℝ) (P A Q : Finset ℕ)
    (hab : a ≤ b) (hce : c ≤ e) (hD : 0 < D) (hd : 0 < d)
    (hcop : Nat.Coprime D d) (hsq : Squarefree d)
    (hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p)
    (hQprime : ∀ p ∈ Q, p.Prime) :
    |(pairSieveData a b c e D W P A Q hD hQprime).remainder d| ≤
      4 * (D : ℝ) * (d : ℝ) ^ 2 +
        2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * (d : ℝ) := by
  classical
  let S := pairSieveData a b c e D W P A Q hD hQprime
  let r := D * d
  letI : NeZero r := ⟨Nat.ne_of_gt (Nat.mul_pos hD hd)⟩
  let R : Finset (ZMod r × ZMod r) := Finset.univ.filter fun v =>
    pairBaseReduction D d v.1 * pairBaseReduction D d v.2 = 1 ∧
      ∀ p : d.primeFactors,
        pairBadLocal p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A))
          (pairPrimeReduction D d p v.1, pairPrimeReduction D d p v.2)
  let width : ℝ := ((b - a : ℕ) : ℝ) * (e - c : ℕ)
  let countSubtype : ℝ :=
    ∏ p : d.primeFactors,
      (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
        (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)
  let rootMain : ℝ :=
    (Nat.totient D : ℝ) * countSubtype * width / (r : ℝ) ^ 2
  have hX : S.X =
      (Nat.totient D : ℝ) * width / (D : ℝ) ^ 2 := by
    simp [S, pairSieveData, width]
    <;> ring
  have hlocalDensity (p : d.primeFactors) :
      S.density p.val =
        (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ) / (p.val : ℝ) ^ 2 := by
    change pairDensity p.val (decide ((p.val : ℝ) ≤ W))
      (decide (p.val ∉ P ∨ p.val ∉ A)) = _
    rw [pairDensity, ← pairBadCount_cast_eq_pairNu p.val (hd3 p.val p.property)]
  have hG : S.g d =
      (∏ p ∈ d.primeFactors,
        (pairBadCount p (decide ((p : ℝ) ≤ W))
          (decide (p ∉ P ∨ p ∉ A)) : ℝ)) / (d : ℝ) ^ 2 := by
    change (∏ p ∈ d.primeFactors, S.density p) = _
    calc
      _ = ∏ p ∈ d.primeFactors,
          (pairBadCount p (decide ((p : ℝ) ≤ W))
            (decide (p ∉ P ∨ p ∉ A)) : ℝ) / (p : ℝ) ^ 2 := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hlocalDensity ⟨p, hp⟩
      _ = (∏ p ∈ d.primeFactors,
            (pairBadCount p (decide ((p : ℝ) ≤ W))
              (decide (p ∉ P ∨ p ∉ A)) : ℝ)) /
          (d : ℝ) ^ 2 := by
        rw [Finset.prod_div_distrib]
        have hprimeProduct :
            (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
          rw [← Nat.cast_prod]
          exact_mod_cast Nat.prod_primeFactors_of_squarefree hsq
        rw [Finset.prod_pow, hprimeProduct]
  have hcountProduct :
      (∏ p : d.primeFactors,
        (pairBadCount p.val (decide ((p.val : ℝ) ≤ W))
          (decide (p.val ∉ P ∨ p.val ∉ A)) : ℝ)) =
      ∏ p ∈ d.primeFactors,
        (pairBadCount p (decide ((p : ℝ) ≤ W))
          (decide (p ∉ P ∨ p ∉ A)) : ℝ) := by
    exact Finset.prod_coe_sort (d.primeFactors : Finset ℕ)
      (fun p : ℕ => (pairBadCount p (decide ((p : ℝ) ≤ W))
        (decide (p ∉ P ∨ p ∉ A)) : ℝ))
  have hcenter : S.X * S.g d = rootMain := by
    rw [hX, hG, ← hcountProduct]
    dsimp [rootMain, countSubtype, width, r]
    rw [Nat.cast_mul]
    have hDc : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
    have hdc : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp [hDc, hdc]
    <;> ring_nf
  have hfilter0 := pairSieveData_local_filter_eq_crtRoots
    a b c e D d W P A Q hD hQprime
  have hfilterS :
      (S.objects.filter fun z => ∀ p ∈ d.primeFactors, S.bad p z) =
        (Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
          (fun z => pairResidue r z ∈ R) := by
    simpa [S, r, R] using hfilter0
  have hrem : S.remainder d =
      ((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
        (fun z => pairResidue r z ∈ R)).card - S.X * S.g d := by
    have hw : ∀ z ∈ S.objects, S.weight z = 1 := by intro z hz; rfl
    rw [sieveRemainder_eq_filtered_card S d hw, hfilterS]
  have hcrt := pair_grid_crt_remainder_bound a b c e D d W P A
    hab hce hD hd hcop hsq hd3
  have hbound :
      |((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
          (fun z => pairResidue r z ∈ R)).card - rootMain| ≤
        (D : ℝ) * (d : ℝ) ^ 2 *
          (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := by
    convert hcrt using 1 <;> simp [R, rootMain, countSubtype, width, r] <;> ring_nf
    <;> ring
  rw [hrem, hcenter]
  calc
    |((Finset.product (Finset.Ico a b) (Finset.Ico c e)).filter
        (fun z => pairResidue r z ∈ R)).card - rootMain| ≤
      (D : ℝ) * (d : ℝ) ^ 2 *
        (4 + 2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) / (r : ℝ)) := hbound
    _ = 4 * (D : ℝ) * (d : ℝ) ^ 2 +
        2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * (d : ℝ) := by
      rw [Nat.cast_mul]
      have hDc : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      have hdc : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
      field_simp [hDc, hdc]
      <;> ring

theorem pairSieveData_remainderSum_bound
    (a b c e D : ℕ) (W z : ℝ) (P A Q : Finset ℕ)
    (hab : a ≤ b) (hce : c ≤ e)
    (hD : 0 < D) (hQprime : ∀ p ∈ Q, p.Prime)
    (hQlarge : ∀ p ∈ Q, 3 ≤ p) (hQnotD : ∀ p ∈ Q, ¬p ∣ D)
    (hQallowed : A ⊆ Q) :
    let S := pairSieveData a b c e D W P A Q hD hQprime
    S.remainderSum z ≤
      4 * (D : ℝ) * (⌊z⌋₊ : ℝ) ^ 3 +
        2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * (⌊z⌋₊ : ℝ) ^ 2 := by
  classical
  let S := pairSieveData a b c e D W P A Q hD hQprime
  let level := ⌊z⌋₊
  have hsubset : S.products z ⊆ Finset.Icc 1 level := by
    exact Finset.filter_subset _ _
  have herror : ∀ d ∈ S.products z,
      |S.remainder d| ≤
        4 * (D : ℝ) * (d : ℝ) ^ 2 +
          2 * (((b - a : ℕ) : ℝ) + (e - c : ℕ)) * (d : ℝ) := by
    intro d hdS
    have hmem := Finset.mem_filter.mp hdS
    have hd1 := (Finset.mem_Icc.mp hmem.1).1
    rcases hmem.2 with ⟨hsq, hdPrimes⟩
    have hdpos : 0 < d := by omega
    have hcop : Nat.Coprime D d := by
      by_contra hnotcop
      obtain ⟨p, hp, hpD, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnotcop
      have hpFactor : p ∈ d.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.ne_of_gt hdpos⟩
      have hpQ : p ∈ Q := hdPrimes hpFactor
      exact hQnotD p hpQ hpD
    have hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p := by
      intro p hp
      exact hQlarge p (hdPrimes hp)
    exact pairSieveData_remainder_bound a b c e D d W P A Q
      hab hce hD hdpos hcop hsq hd3 hQprime
  have hsum := sum_remainder_errors_level_bound level
    (D : ℝ) (((b - a : ℕ) : ℝ) + (e - c : ℕ))
    (by positivity) (by positivity) (S.products z) hsubset S.remainder herror
  simpa [S, level, Erdos821.Blueprint.SieveData.remainderSum] using hsum

theorem pairSieveData_product_eq_pairFiniteProduct
    (a b c e D : ℕ) (W z : ℝ) (P A Q : Finset ℕ)
    (hD : 0 < D) (hz0 : 0 ≤ z)
    (hQsubset : Q ⊆ Erdos821.Blueprint.primesUpTo z)
    (hQcomplete : ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ p ∣ D → p ∈ Q)
    (hQprime : ∀ p ∈ Q, p.Prime) (hQlarge : ∀ p ∈ Q, 3 ≤ p)
    (hQnotD : ∀ p ∈ Q, ¬p ∣ D) :
    (pairSieveData a b c e D W P A Q hD hQprime).product =
      pairFiniteProduct (Erdos821.Blueprint.primesUpTo z) W D P A := by
  classical
  let Qall := Erdos821.Blueprint.primesUpTo z
  let S := pairSieveData a b c e D W P A Q hD hQprime
  have hextra : ∀ p ∈ Qall \ Q, pairLocalFactor p W D P A = 1 := by
    intro p hp
    have hpAll := (Finset.mem_sdiff.mp hp).1
    have hpData := (Erdos821.P9Core.mem_primesUpTo_iff z hz0 p).1 hpAll
    have hpPrime := hpData.1
    have hpz := hpData.2
    by_cases hp2 : p = 2
    · subst p
      simp [pairLocalFactor]
    · have hp2le : 2 ≤ p := hpPrime.two_le
      have hp3 : 3 ≤ p := by omega
      have hpD : p ∣ D := by
        by_contra hpD
        exact (Finset.mem_sdiff.mp hp).2 (hQcomplete p hpPrime hp3 hpz hpD)
      simp [pairLocalFactor, hp3, hpD]
  have hprod :
      pairFiniteProduct Qall W D P A =
        ∏ p ∈ Q, pairLocalFactor p W D P A := by
    rw [pairFiniteProduct]
    calc
      (∏ p ∈ Qall, pairLocalFactor p W D P A) =
          (∏ p ∈ Qall \ Q, pairLocalFactor p W D P A) *
            (∏ p ∈ Q, pairLocalFactor p W D P A) :=
        (Finset.prod_sdiff hQsubset).symm
      _ = (∏ p ∈ Qall \ Q, (1 : ℝ)) *
            (∏ p ∈ Q, pairLocalFactor p W D P A) := by
        congr 1
        apply Finset.prod_congr rfl
        intro p hp
        exact hextra p hp
      _ = _ := by simp
  have hlocal : ∀ p ∈ Q,
      pairLocalFactor p W D P A =
        1 - pairDensity p (decide ((p : ℝ) ≤ W))
          (decide (p ∉ P ∨ p ∉ A)) := by
    intro p hp
    have hp3 := hQlarge p hp
    have hpD := hQnotD p hp
    simp [pairLocalFactor, hp3, hpD]
  calc
    S.product = ∏ p ∈ Q,
        (1 - pairDensity p (decide ((p : ℝ) ≤ W))
          (decide (p ∉ P ∨ p ∉ A))) := by
      rfl
    _ = ∏ p ∈ Q, pairLocalFactor p W D P A := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (hlocal p hp).symm
    _ = pairFiniteProduct Qall W D P A := hprod.symm

theorem pairSieveData_densityBounds
    (a b c e D : ℕ) (W z : ℝ) (P A Q : Finset ℕ)
    (hD : 0 < D) (hW2 : 2 ≤ W) (hWz : W ≤ z) (hz : 1 < z)
    (hQsubset : Q ⊆ Erdos821.Blueprint.primesUpTo z)
    (hQprime : ∀ p ∈ Q, p.Prime) (hQlarge : ∀ p ∈ Q, 3 ≤ p)
    (hQnotD : ∀ p ∈ Q, ¬ p ∣ D)
    (hPsubset : P ⊆ Erdos821.Blueprint.primesUpTo W) (hAsubset : A ⊆ P)
    (hM : ∃ K : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ Erdos821.Blueprint.primesUpTo y, (p : ℝ)⁻¹) -
        Real.log (Real.log y)| ≤ K) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      (pairSieveData a b c e D W P A Q hD hQprime).densityBounds z (2 / 9) C₀ := by
  classical
  obtain ⟨K, hK⟩ := hM
  have hK0 : 0 ≤ K := by
    have htwo := hK 2 (by norm_num)
    exact le_trans (abs_nonneg _) htwo
  let C₀ : ℝ := 3 * (Real.log 2 + 2 * K) + 1
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  let S := pairSieveData a b c e D W P A Q hD hQprime
  have hInterval (w : ℝ) (hw : 1 < w) :
      (∑ p ∈ Q.filter fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ 2,
        S.density p) ≤ C₀ := by
    let I := Q.filter fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ 2
    have hlocal (p : ℕ) (hp : p ∈ I) :
        S.density p ≤ 3 / (p : ℝ) := by
      have hpQ := (Finset.mem_filter.mp hp).1
      have hpP := hQprime p hpQ
      have hp3 := hQlarge p hpQ
      simpa [S, pairSieveData] using (pair_density_bound p hpP hp3
        (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))).2.1
    have hIle : (∑ p ∈ I, S.density p) ≤ 3 * (∑ p ∈ I, (p : ℝ)⁻¹) := by
      calc
        _ ≤ ∑ p ∈ I, 3 / (p : ℝ) := Finset.sum_le_sum (by
          intro p hp
          exact hlocal p hp)
        _ = 3 * (∑ p ∈ I, (p : ℝ)⁻¹) := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.mul_sum]
    by_cases hw2 : 2 ≤ w
    · let Qlo := Erdos821.Blueprint.primesUpTo w
      let Qhi := Erdos821.Blueprint.primesUpTo (w ^ 2)
      have hWw2 : w ≤ w ^ 2 := by nlinarith
      have hQlo : Qlo ⊆ Qhi := by
        apply Erdos821.P9Core.primesUpTo_mono hWw2 (by linarith) (by positivity)
      have hIsub : I ⊆ Qhi \ Qlo := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpQ, ⟨hwp, hpw2⟩⟩
        have hpPrime := hQprime p hpQ
        have hpHi : p ∈ Qhi :=
          (Erdos821.P9Core.mem_primesUpTo_iff (w ^ 2) (by positivity) p).2
            ⟨hpPrime, hpw2⟩
        have hpNotLo : p ∉ Qlo := by
          intro hpLo
          exact (not_lt_of_ge
            ((Erdos821.P9Core.mem_primesUpTo_iff w (by linarith) p).1 hpLo).2) hwp
        exact Finset.mem_sdiff.mpr ⟨hpHi, hpNotLo⟩
      have hrecipDiff : (∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹) =
          (∑ p ∈ Qhi, (p : ℝ)⁻¹) - ∑ p ∈ Qlo, (p : ℝ)⁻¹ := by
        have hsum :
            (∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹) +
                ∑ p ∈ Qlo, (p : ℝ)⁻¹ =
              ∑ p ∈ Qhi, (p : ℝ)⁻¹ := Finset.sum_sdiff hQlo
        linarith
      have hhighBound :
          (∑ p ∈ Qhi, (p : ℝ)⁻¹) - Real.log (Real.log (w ^ 2)) ≤ K := by
        have h := hK (w ^ 2) (by nlinarith)
        exact (abs_le.mp h).2
      have hlowBound : Real.log (Real.log w) -
          (∑ p ∈ Qlo, (p : ℝ)⁻¹) ≤ K := by
        have h := hK w (by linarith)
        have hleft := (abs_le.mp h).1
        linarith
      have hlogRatio : Real.log (Real.log (w ^ 2)) - Real.log (Real.log w) =
          Real.log 2 := by
        have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
        rw [Real.log_pow]
        norm_num1
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlogw)]
        ring
      have hrecipI : (∑ p ∈ I, (p : ℝ)⁻¹) ≤ Real.log 2 + 2 * K := by
        calc
          (∑ p ∈ I, (p : ℝ)⁻¹) ≤ ∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hIsub (by
              intro p hp hnot
              have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
              exact inv_nonneg.mpr hp0)
          _ = (∑ p ∈ Qhi, (p : ℝ)⁻¹) - ∑ p ∈ Qlo, (p : ℝ)⁻¹ := hrecipDiff
          _ ≤ Real.log (Real.log (w ^ 2)) - Real.log (Real.log w) + 2 * K := by
            linarith [hhighBound, hlowBound]
          _ = Real.log 2 + 2 * K := by rw [hlogRatio]
      have hILeC : (∑ p ∈ I, S.density p) ≤ C₀ := by
        calc
          _ ≤ 3 * (∑ p ∈ I, (p : ℝ)⁻¹) := hIle
          _ ≤ 3 * (Real.log 2 + 2 * K) := mul_le_mul_of_nonneg_left hrecipI (by norm_num)
          _ ≤ C₀ := by dsimp [C₀]; linarith
      simpa [I] using hILeC
    · have hwLt : w < 2 := lt_of_not_ge hw2
      have hwSq : w ^ 2 < 4 := by nlinarith
      have hIone : I ⊆ {3} := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpQ, ⟨hwp, hpw2⟩⟩
        have hpNat : 3 ≤ p := hQlarge p hpQ
        have hpLt : (p : ℝ) < 4 := lt_of_le_of_lt hpw2 hwSq
        have hpNatLt : p < 4 := by exact_mod_cast hpLt
        have hpeq : p = 3 := by omega
        simp [hpeq]
      have hIleOne : (∑ p ∈ I, S.density p) ≤ 1 := by
        calc
          _ ≤ ∑ p ∈ I, 1 := Finset.sum_le_sum (by
            intro p hp
            have hpQ := (Finset.mem_filter.mp hp).1
            have h := (pair_density_bound p (hQprime p hpQ) (hQlarge p hpQ)
              (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))).2.2
            simpa [S, pairSieveData] using (h.trans (by norm_num : (7 / 9 : ℝ) ≤ 1)))
          _ ≤ ∑ p ∈ ({3} : Finset ℕ), (1 : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hIone (by intro p hp hnot; norm_num)
          _ = 1 := by simp
      have hILeC : (∑ p ∈ I, S.density p) ≤ C₀ := by
        calc
          _ ≤ 1 := hIleOne
          _ ≤ C₀ := by dsimp [C₀]; linarith [hK0, Real.log_nonneg (by norm_num : (1:ℝ)≤2)]
      simpa [I] using hILeC
  refine ⟨C₀, hC₀, ?_⟩
  refine ⟨hz, by norm_num, ?_, ?_⟩
  · intro p hp
    have hpQ := hQprime p hp
    have hpz := (Erdos821.P9Core.mem_primesUpTo_iff z (by linarith) p).1 (hQsubset hp)
    have hlocal := pair_density_bound p hpQ (hQlarge p hp)
      (decide ((p : ℝ) ≤ W)) (decide (p ∉ P ∨ p ∉ A))
    constructor
    · exact hpz.2
    constructor
    · exact hlocal.1
    · have hDensity : S.density p ≤ 7 / 9 := by
        simpa [S, pairSieveData] using hlocal.2.2
      calc
        S.density p ≤ 7 / 9 := hDensity
        _ ≤ 1 - 2 / 9 := by norm_num
  · intro w hw
    simpa [S, pairSieveData] using hInterval w hw

theorem block_sieve_upper_bound
    (hs : Erdos821.Blueprint.SieveInputs) (η C₀ z : ℝ)
    (hη : 0 < η) (hC₀ : 0 < C₀)
    (S : Erdos821.Blueprint.SieveData (ℕ × ℕ))
    (hDensity : S.densityBounds z η C₀) :
    ∃ K : ℝ, 0 < K ∧
      S.sifted ≤ K * S.X * S.product + K * S.remainderSum (z ^ (10 : ℕ)) := by
  obtain ⟨K, hK, h₀, hBlock⟩ := hs.block η C₀ hη hC₀
  exact ⟨K, hK, (hBlock (ℕ × ℕ) S z hDensity).1⟩





end

end Erdos821.P9Core
