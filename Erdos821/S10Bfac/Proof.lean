import Erdos821.S10.BalancedTasks

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.S10Bfac

open Erdos821.Blueprint Erdos821.P10 Erdos821.P7Core
attribute [local instance] Classical.propDecidable

theorem balanced_factorization_of_support
    {x κ : ℝ} (hx : 1 < x) (hκ : 0 < κ) (hκ' : κ < 1 / 50)
    (hbigκ : 5 ≤ x ^ κ)
    (hbig3 : 5 ≤ x ^ (3 * (1 / 2 - κ) - 1))
    {u : ℕ} (hu : x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hcomp : ¬ Nat.Prime (2 * u + 1))
    (hmin : x ^ (1 / 2 - κ) < (Nat.minFac (2 * u + 1) : ℝ)) :
    Nat.Prime (Nat.minFac (2 * u + 1)) ∧
      Nat.Prime ((2 * u + 1) / (Nat.minFac (2 * u + 1))) ∧
      Nat.minFac (2 * u + 1) * ((2 * u + 1) / (Nat.minFac (2 * u + 1))) =
        2 * u + 1 ∧
      x ^ (1 / 2 - 2 * κ) ≤ (Nat.minFac (2 * u + 1) : ℝ) ∧
      (Nat.minFac (2 * u + 1) : ℝ) ≤ x ^ (1 / 2 + 2 * κ) ∧
      x ^ (1 / 2 - 2 * κ) ≤ (((2 * u + 1) / Nat.minFac (2 * u + 1) : ℕ) : ℝ) ∧
      (((2 * u + 1) / Nat.minFac (2 * u + 1) : ℕ) : ℝ) ≤ x ^ (1 / 2 + 2 * κ) := by
  let N : ℕ := 2 * u + 1
  let p : ℕ := N.minFac
  let q : ℕ := N / p
  let α : ℝ := 1 / 2 - κ
  let β : ℝ := 1 / 2 + 2 * κ
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have huTwo : 2 ≤ u := by
    have huOneReal : (1 : ℝ) < (u : ℝ) := lt_of_lt_of_le hx hu.1
    have huOneNat : 1 < u := by exact_mod_cast huOneReal
    omega
  have hNpos : 0 < N := by dsimp [N]; omega
  have hNge : 2 ≤ N := by dsimp [N]; omega
  have hpPrime : Nat.Prime p := by
    apply Nat.minFac_prime
    dsimp [p, N]
    omega
  have hpDvd : p ∣ N := by
    dsimp [p]
    exact Nat.minFac_dvd N
  have hqMul : q * p = N := by
    dsimp [q]
    exact Nat.div_mul_cancel hpDvd
  have hpqMul : p * q = N := by
    calc
      p * q = q * p := Nat.mul_comm _ _
      _ = N := hqMul
  have hpLower : x ^ α < (p : ℝ) := by
    simpa [α, p, N] using hmin
  have hqPos : 0 < q := by
    have hpLeN : p ≤ N := Nat.le_of_dvd hNpos hpDvd
    exact Nat.div_pos hpLeN hpPrime.pos
  have hqGe : 2 ≤ q := by
    by_contra h
    have hqLe : q ≤ 1 := by omega
    have hqeq : q = 1 := by omega
    have hpEqN : p = N := by simpa [hqeq] using hqMul
    have hpN : Nat.Prime N := by rw [← hpEqN]; exact hpPrime
    exact hcomp hpN
  have hqDivN : q ∣ N := by
    exact ⟨p, hqMul.symm⟩
  have hqPrime : Nat.Prime q := by
    by_contra hqNotPrime
    obtain ⟨r, hrPrime, hrDvdQ, hrLtQ⟩ :=
      Erdos821.P10.composite_has_proper_prime_factor hqGe hqNotPrime
    let s : ℕ := q / r
    have hsMul : s * r = q := by
      dsimp [s]
      exact Nat.div_mul_cancel hrDvdQ
    have hsPos : 0 < s := by
      dsimp [s]
      exact Nat.div_pos (Nat.le_of_dvd hqPos hrDvdQ) hrPrime.pos
    have hsNeOne : s ≠ 1 := by
      intro hs
      have hqEqR : q = r := by
        have h := hsMul
        rw [hs] at h
        simpa [Nat.mul_comm] using h.symm
      omega
    have hsGe : 2 ≤ s := by omega
    have hsDvdQ : s ∣ q := ⟨r, hsMul.symm⟩
    have hsDvdN : s ∣ N := dvd_trans hsDvdQ hqDivN
    have hrDvdN : r ∣ N := dvd_trans hrDvdQ hqDivN
    have hsMinPrime : Nat.Prime s.minFac := Nat.minFac_prime (by omega)
    have hsMinDvdN : s.minFac ∣ N := dvd_trans (Nat.minFac_dvd s) hsDvdN
    have hMinLeR : p ≤ r := by
      exact Nat.minFac_le_of_dvd hrPrime.two_le hrDvdN
    have hMinLeSMin : p ≤ s.minFac := by
      exact Nat.minFac_le_of_dvd hsMinPrime.two_le hsMinDvdN
    have hSMinLe : s.minFac ≤ s := Nat.minFac_le hsPos
    have hMinLeS : p ≤ s := hMinLeSMin.trans hSMinLe
    have hrLower : x ^ α < (r : ℝ) :=
      lt_of_lt_of_le hpLower (Nat.cast_le.mpr hMinLeR)
    have hsLower : x ^ α < (s : ℝ) :=
      lt_of_lt_of_le hpLower (Nat.cast_le.mpr hMinLeS)
    have hαpos : 0 < x ^ α := Real.rpow_pos_of_pos hxpos α
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hrPos : 0 < (r : ℝ) := by exact_mod_cast hrPrime.pos
    have hpr : (x ^ α) * (x ^ α) < (p : ℝ) * (r : ℝ) := by
      calc
        (x ^ α) * (x ^ α) < (p : ℝ) * (x ^ α) :=
          mul_lt_mul_of_pos_right hpLower hαpos
        _ < (p : ℝ) * (r : ℝ) :=
          mul_lt_mul_of_pos_left hrLower hpPos
    have hprs : ((x ^ α) * (x ^ α)) * (x ^ α) <
        ((p : ℝ) * (r : ℝ)) * (s : ℝ) := by
      calc
        ((x ^ α) * (x ^ α)) * (x ^ α) < ((p : ℝ) * (r : ℝ)) * (x ^ α) :=
          mul_lt_mul_of_pos_right hpr hαpos
        _ < ((p : ℝ) * (r : ℝ)) * (s : ℝ) :=
          mul_lt_mul_of_pos_left hsLower (mul_pos hpPos hrPos)
    have hpow3 : (x ^ α) * (x ^ α) * (x ^ α) = x ^ (3 * α) := by
      calc
        (x ^ α) * (x ^ α) * (x ^ α) = x ^ (α + α) * (x ^ α) := by
          rw [← Real.rpow_add hxpos]
        _ = x ^ ((α + α) + α) := by
          rw [← Real.rpow_add hxpos]
        _ = x ^ (3 * α) := by congr 1 <;> ring
    have hfactor : p * r * s = N := by
      calc
        p * r * s = p * (s * r) := by ring
        _ = p * q := by rw [hsMul]
        _ = N := hpqMul
    have hfactorR : (p : ℝ) * (r : ℝ) * (s : ℝ) = (N : ℝ) := by
      exact_mod_cast hfactor
    have hlowerN : x ^ (3 * α) < (N : ℝ) := by
      calc
        x ^ (3 * α) = (x ^ α) * (x ^ α) * (x ^ α) := hpow3.symm
        _ < (p : ℝ) * (r : ℝ) * (s : ℝ) := hprs
        _ = (N : ℝ) := hfactorR
    have hNupper : (N : ℝ) ≤ 5 * x := by
      dsimp [N]
      push_cast
      nlinarith [hu.2, hxone]
    have hlarge3 : 5 * x ≤ x ^ (3 * α) := by
      have heq : 3 * α - 1 + 1 = 3 * α := by ring
      have hmul : x ^ (3 * α - 1) * x = x ^ (3 * α) := by
        calc
          x ^ (3 * α - 1) * x = x ^ (3 * α - 1) * x ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = x ^ (3 * α - 1 + 1) := by rw [← Real.rpow_add hxpos]
          _ = x ^ (3 * α) := by rw [heq]
      calc
        5 * x ≤ x ^ (3 * α - 1) * x :=
          mul_le_mul_of_nonneg_right (by simpa [α] using hbig3)
            (le_trans (by norm_num : (0 : ℝ) ≤ 1) hxone)
        _ = x ^ (3 * α) := hmul
    have hcontr : x ^ (3 * α) < x ^ (3 * α) := by
      calc
        x ^ (3 * α) < (N : ℝ) := hlowerN
        _ ≤ 5 * x := hNupper
        _ ≤ x ^ (3 * α) := hlarge3
    exact (lt_irrefl _ hcontr)
  have hqLower : x ^ α < (q : ℝ) := by
    have hMinLeQ : p ≤ q := Nat.minFac_le_of_dvd hqPrime.two_le hqDivN
    exact lt_of_lt_of_le hpLower (Nat.cast_le.mpr hMinLeQ)
  have hNupper : (N : ℝ) ≤ 5 * x := by
    dsimp [N]
    push_cast
    nlinarith [hu.2, hxone]
  have hfactorR : (p : ℝ) * (q : ℝ) = (N : ℝ) := by exact_mod_cast hpqMul
  have hαpos : 0 < x ^ α := Real.rpow_pos_of_pos hxpos α
  have hTargetUpper : 5 * x ≤ x ^ β * x ^ α := by
    calc
      5 * x ≤ x ^ κ * x := mul_le_mul_of_nonneg_right hbigκ
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hxone)
      _ = x ^ β * x ^ α := by
        symm
        calc
          x ^ β * x ^ α = x ^ (β + α) := by rw [← Real.rpow_add hxpos]
          _ = x ^ (κ + 1) := by congr 1 <;> dsimp [α, β] <;> ring
          _ = x ^ κ * x ^ (1 : ℝ) := by rw [← Real.rpow_add hxpos]
          _ = x ^ κ * x := by rw [Real.rpow_one]
  have hpUpper : (p : ℝ) ≤ x ^ β := by
    have hmulLower : (p : ℝ) * x ^ α ≤ (p : ℝ) * (q : ℝ) :=
      mul_le_mul_of_nonneg_left hqLower.le (by positivity)
    have hmulUpper : (p : ℝ) * x ^ α ≤ x ^ β * x ^ α := by
      calc
        (p : ℝ) * x ^ α ≤ (p : ℝ) * (q : ℝ) := hmulLower
        _ = (N : ℝ) := hfactorR
        _ ≤ 5 * x := hNupper
        _ ≤ x ^ β * x ^ α := hTargetUpper
    by_contra hnot
    have hlt : x ^ β < (p : ℝ) := lt_of_not_ge hnot
    have hmul : x ^ β * x ^ α < (p : ℝ) * x ^ α :=
      mul_lt_mul_of_pos_right hlt hαpos
    linarith
  have hqUpper : (q : ℝ) ≤ x ^ β := by
    have hmulLower : (q : ℝ) * x ^ α ≤ (q : ℝ) * (p : ℝ) :=
      mul_le_mul_of_nonneg_left hpLower.le (by positivity)
    have hmulUpper : (q : ℝ) * x ^ α ≤ x ^ β * x ^ α := by
      calc
        (q : ℝ) * x ^ α ≤ (q : ℝ) * (p : ℝ) := hmulLower
        _ = (N : ℝ) := by rw [mul_comm]; exact hfactorR
        _ ≤ 5 * x := hNupper
        _ ≤ x ^ β * x ^ α := hTargetUpper
    by_contra hnot
    have hlt : x ^ β < (q : ℝ) := lt_of_not_ge hnot
    have hmul : x ^ β * x ^ α < (q : ℝ) * x ^ α :=
      mul_lt_mul_of_pos_right hlt hαpos
    linarith
  have hwindowLower : x ^ (1 / 2 - 2 * κ) ≤ x ^ α :=
    Real.rpow_le_rpow_of_exponent_le hxone (by dsimp [α]; linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [p, N] using hpPrime
  · simpa [q, p, N] using hqPrime
  · simpa [q, p, N] using hpqMul
  · simpa [p, N, α] using hwindowLower.trans hpLower.le
  · simpa [p, N, β] using hpUpper
  · simpa [q, p, N, α] using hwindowLower.trans hqLower.le
  · simpa [q, p, N, β] using hqUpper

theorem eventually_balanced_factor_thresholds {κ : ℝ} (hκ : 0 < κ)
    (hκ' : κ < 1 / 50) :
    ∀ᶠ x : ℝ in atTop,
      1 < x ∧ 5 ≤ x ^ κ ∧ 5 ≤ x ^ (3 * (1 / 2 - κ) - 1) := by
  have he : 0 < 3 * (1 / 2 - κ) - 1 := by nlinarith
  have hkTop : Tendsto (fun x : ℝ => x ^ κ) atTop atTop := tendsto_rpow_atTop hκ
  have heTop : Tendsto (fun x : ℝ => x ^ (3 * (1 / 2 - κ) - 1)) atTop atTop :=
    tendsto_rpow_atTop he
  filter_upwards
    [eventually_gt_atTop (1 : ℝ), hkTop.eventually (eventually_ge_atTop (5 : ℝ)),
      heTop.eventually (eventually_ge_atTop (5 : ℝ))]
    with x hx hk h3
  exact ⟨hx, hk, h3⟩

def balancedPrimePairTerm (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (z : ℕ × ℕ) : ℝ :=
  if Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 then
    C.weighted x jstar ((z.1 * z.2 - 1) / 2) *
      test .prime x z.1 * test .prime x z.2
  else 0

theorem balanced_prime_window_mass_eq_pair_sum
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (κ : ℝ) :
    balancedPrimeWindowMass C x jstar κ =
      ∑ z ∈ balancedWindow x κ ×ˢ balancedWindow x κ,
        balancedPrimePairTerm C x jstar z := by
  classical
  unfold balancedPrimeWindowMass balancedPairWindowMass
  change (∑ m ∈ balancedWindow x κ, ∑ n ∈ balancedWindow x κ,
      balancedPrimePairTerm C x jstar (m, n)) = _
  exact (Finset.sum_product (balancedWindow x κ) (balancedWindow x κ)
    (balancedPrimePairTerm C x jstar)).symm

theorem BalancedFactorCoverageTask_proof : BalancedFactorCoverageTask := by
  intro δ C hBounds κ hκ hκ' jstar hj
  rcases hBounds with ⟨K, CA, cmin, cmax, hK, hcmin, hcmax, hbounded⟩
  have hboundEvent := hbounded jstar hj
  have hthresholdEvent := eventually_balanced_factor_thresholds hκ hκ'
  filter_upwards [hboundEvent, hthresholdEvent] with x hxBound hxThreshold
  rcases hxThreshold with ⟨hx, hbigκ, hbig3⟩
  rcases hxBound with ⟨_, _, _, hweightNonneg, _, hweightSupport⟩
  have hSupport : ∀ u, C.weighted x jstar u ≠ 0 →
      x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x := by
    intro u hu
    exact ⟨(hweightSupport u hu).1, (hweightSupport u hu).2.1⟩
  let U : Finset ℕ := (Finset.Icc 1 ⌊2 * x⌋₊).filter
    (fun u => ¬ Nat.Prime (2 * u + 1) ∧
      x ^ (1 / 2 - κ) < (Nat.minFac (2 * u + 1) : ℝ))
  let S : Finset ℕ := U.filter (fun u => C.weighted x jstar u ≠ 0)
  let W : Finset ℕ := balancedWindow x κ
  let R : Finset (ℕ × ℕ) := W ×ˢ W
  let φ : ℕ → ℕ × ℕ := fun u =>
    (Nat.minFac (2 * u + 1), (2 * u + 1) / Nat.minFac (2 * u + 1))
  let g : ℕ × ℕ → ℝ := balancedPrimePairTerm C x jstar
  have hCover : ∀ u ∈ S,
      Nat.Prime (φ u).1 ∧ Nat.Prime (φ u).2 ∧
        (φ u).1 * (φ u).2 = 2 * u + 1 ∧
        (φ u).1 ∈ W ∧ (φ u).2 ∈ W := by
    intro u huS
    rcases Finset.mem_filter.mp huS with ⟨huU, hweightNe⟩
    rcases Finset.mem_filter.mp huU with ⟨_, hpred⟩
    rcases hpred with ⟨hcomp, hmin⟩
    have huSupport := hSupport u hweightNe
    rcases balanced_factorization_of_support hx hκ hκ' hbigκ hbig3
        huSupport hcomp hmin with
      ⟨hp, hq, hmul, hpLo, hpHi, hqLo, hqHi⟩
    have hpWindow : Nat.minFac (2 * u + 1) ∈ W := by
      change Nat.minFac (2 * u + 1) ∈ balancedWindow x κ
      rw [balancedWindow, Finset.mem_Icc]
      exact ⟨Nat.ceil_le.mpr hpLo,
        (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ x ^ (1 / 2 + 2 * κ))).mpr hpHi⟩
    have hqWindow :
        (2 * u + 1) / Nat.minFac (2 * u + 1) ∈ W := by
      change (2 * u + 1) / Nat.minFac (2 * u + 1) ∈ balancedWindow x κ
      rw [balancedWindow, Finset.mem_Icc]
      exact ⟨Nat.ceil_le.mpr hqLo,
        (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ x ^ (1 / 2 + 2 * κ))).mpr hqHi⟩
    exact ⟨hp, hq, hmul, hpWindow, hqWindow⟩
  have hSource : balancedCompositeMass C x jstar κ =
      ∑ u ∈ S, C.weighted x jstar u := by
    unfold balancedCompositeMass
    change (∑ u ∈ U, C.weighted x jstar u) = _
    symm
    change (∑ u ∈ U.filter (fun u => C.weighted x jstar u ≠ 0),
      C.weighted x jstar u) = _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hzero : C.weighted x jstar u = 0 <;> simp [hzero]
  have hpairNonneg : ∀ z ∈ R, 0 ≤ g z := by
    intro z hz
    by_cases hcond : Odd (z.1 * z.2) ∧ 1 < z.1 * z.2
    · have hw := hweightNonneg ((z.1 * z.2 - 1) / 2)
      have htest₁ : 0 ≤ test .prime x z.1 := by
        by_cases hprime : Nat.Prime z.1 <;> simp [test, hprime]
      have htest₂ : 0 ≤ test .prime x z.2 := by
        by_cases hprime : Nat.Prime z.2 <;> simp [test, hprime]
      dsimp [g, balancedPrimePairTerm]
      rw [if_pos hcond]
      exact mul_nonneg (mul_nonneg hw htest₁) htest₂
    · dsimp [g, balancedPrimePairTerm]
      simp [hcond]
  have hTerm : ∀ u ∈ S, C.weighted x jstar u = g (φ u) := by
    intro u huS
    rcases hCover u huS with ⟨hp, hq, hmul, _, _⟩
    have huU : u ∈ U := (Finset.mem_filter.mp huS).1
    have huIcc : u ∈ Finset.Icc 1 ⌊2 * x⌋₊ :=
      (Finset.mem_filter.mp huU).1
    have huOne : 1 ≤ u := (Finset.mem_Icc.mp huIcc).1
    have hodd : Odd ((φ u).1 * (φ u).2) := ⟨u, hmul⟩
    have hgt : 1 < (φ u).1 * (φ u).2 := by rw [hmul]; omega
    have hshift : ((φ u).1 * (φ u).2 - 1) / 2 = u := by
      rw [hmul]
      omega
    dsimp [g, balancedPrimePairTerm]
    rw [if_pos ⟨hodd, hgt⟩, hshift]
    simp [test, hp, hq]
  have hinj : Set.InjOn φ (↑S) := by
    intro u₁ hu₁ u₂ hu₂ heq
    have hu₁S : u₁ ∈ S := by simpa using hu₁
    have hu₂S : u₂ ∈ S := by simpa using hu₂
    have hprod₁ := (hCover u₁ hu₁S).2.2.1
    have hprod₂ := (hCover u₂ hu₂S).2.2.1
    have hprodEq : (φ u₁).1 * (φ u₁).2 = (φ u₂).1 * (φ u₂).2 :=
      congrArg (fun z : ℕ × ℕ => z.1 * z.2) heq
    rw [hprod₁, hprod₂] at hprodEq
    omega
  have himage : Finset.image φ S ⊆ R := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨u, huS, rfl⟩
    rcases hCover u huS with ⟨_, _, _, hpWindow, hqWindow⟩
    exact Finset.mem_product.mpr ⟨hpWindow, hqWindow⟩
  have hsumLe :
      (∑ u ∈ S, C.weighted x jstar u) ≤ ∑ z ∈ R, g z := by
    apply Finset.sum_le_sum_of_injOn φ hinj himage
    · intro u huS
      rw [hTerm u huS]
    · intro z hz _
      exact hpairNonneg z hz
  have hpairMass := balanced_prime_window_mass_eq_pair_sum C x jstar κ
  calc
    balancedCompositeMass C x jstar κ =
        ∑ u ∈ S, C.weighted x jstar u := hSource
    _ ≤ ∑ z ∈ R, g z := hsumLe
    _ = balancedPrimeWindowMass C x jstar κ := by
      simpa [R, W, g] using hpairMass.symm

end Erdos821.S10Bfac
