import Erdos821.S9.AssignmentSiftedTask
import Erdos821.P9.AssignmentSieveBridge

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core
attribute [local instance] Classical.propDecidable

theorem candidate_psi_uniform_bound (δ : ℝ) (C : CandidateData)
    (hC : C.Geometry δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ, C.psi y ≤ B := by
  rcases hC with ⟨hvalid, hc₁, hc₂, hratio, hs', hδ, hlast, hprefix, hgap,
    hq, hell, ha, hb, hc, hd, hmicro, hlo, hhi, htheta, hsmall, htail,
    hpsiSmooth, hpsiSupport, hpsiNonneg, hpsiPositive⟩
  have hcontinuous : Continuous C.psi := htail.continuous
  have himage : IsCompact (C.psi '' Set.Icc (1 : ℝ) 2) :=
    isCompact_Icc.image hcontinuous
  obtain ⟨K, hK⟩ := himage.bddAbove
  have hBpos : 0 < max 1 K :=
    lt_of_lt_of_le (by norm_num) (le_max_left (1 : ℝ) K)
  refine ⟨max 1 K, hBpos, ?_⟩
  intro y
  by_cases hy : C.psi y = 0
  · rw [hy]
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left (1 : ℝ) K)
  · have hySupport : y ∈ Function.support C.psi := by
      simpa [Function.support] using hy
    have hyIcc := hpsiSmooth hySupport
    have hval : C.psi y ∈ C.psi '' Set.Icc (1 : ℝ) 2 := ⟨y, hyIcc, rfl⟩
    exact (hK hval).trans (le_max_right (1 : ℝ) K)

theorem assignment_pair_mem_pairBudgetSifted
    (C : CandidateData) (x M N : ℝ) (hx : 0 ≤ x) (jstar : ℕ)
    (micro : MicroAssignments C x jstar)
    (marks : GlobalMarkChoices (C.bands.groups x))
    (allow : PermissionIndex
      (assignmentMaskPrimes C x marks) → Bool)
    (u m n : ℕ) (hprod1 : 1 < m * n)
    (hmn : m * n = 2 * u + 1)
    (hroughM : Analytic.rough (W x) m)
    (hroughN : Analytic.rough (W x) n)
    (hm : m ∈ Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊)
    (hn : n ∈ Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊)
    (hgood : globalAssignmentMaskGood C x jstar u (micro, ⟨marks, allow⟩))
    (hMaskGood : permissionMaskGood (assignmentMaskPrimes C x marks) u allow) :
    let D := assignmentModulus C x jstar micro marks
    let R := assignmentMaskPrimes C x marks
    let S := pairBudgetData C x M N D R
      (assignmentModulus_pos C x jstar micro marks) allow
    (m, n) ∈ S.objects ∧ ∀ p ∈ S.primes, ¬ S.bad p (m, n) := by
  classical
  let G := C.bands.groups x
  let D := assignmentModulus C x jstar micro marks
  let R := assignmentMaskPrimes C x marks
  let P := groupPrimeSet G
  let A := permissionAllowed R allow
  let Q := pairBudgetPrimes C x D
  have huNe : u ≠ 0 := by
    intro huZero
    subst u
    rw [hmn] at hprod1
    norm_num at hprod1
  have hDdiv : D ∣ u := by
    dsimp [D, assignmentModulus]
    exact globalAssignmentMask_divisor_dvd_index G u
      (microAssignmentProduct C x jstar micro) marks hgood.1.1 hgood.2 huNe
  have hQprime : ∀ p ∈ Q, p.Prime := by
    intro p hpQ
    have hmem := (Finset.mem_filter.mp hpQ).1
    have hpositive : 0 ≤ x ^ C.theta := Real.rpow_nonneg hx _
    exact (mem_primesUpTo_iff (x ^ C.theta) hpositive p).1 hmem |>.1
  have hQlarge : ∀ p ∈ Q, 3 ≤ p := by
    intro p hpQ
    exact (Finset.mem_filter.mp hpQ).2.1
  have hnoBanned : ∀ p ∈ Q, p ∉ P ∨ p ∉ A → ¬ p ∣ u := by
    intro p hpQ hban
    have hpData : p ∈ primesUpTo (x ^ C.theta) := (Finset.mem_filter.mp hpQ).1
    have hpPrime := (mem_primesUpTo_iff (x ^ C.theta)
      (Real.rpow_nonneg hx _) p).1 hpData |>.1
    have hpSmall : (p : ℝ) ≤ x ^ C.theta :=
      (mem_primesUpTo_iff (x ^ C.theta)
        (Real.rpow_nonneg hx _) p).1 hpData |>.2
    have hDnot : ¬ p ∣ D := (Finset.mem_filter.mp hpQ).2.2
    have hDnotProduct : ¬ p ∣ microAssignmentProduct C x jstar micro *
        globalMarkProduct G marks := by
      simpa [D, assignmentModulus] using hDnot
    by_cases hpP : p ∈ P
    · by_cases hpMark : p ∈ globalMarkImage G marks
      · intro hpDivU
        have ⟨g, hg, hEq⟩ := Finset.mem_image.mp hpMark
        have hpDvdMark : (marks g).val ∣ globalMarkProduct G marks := by
          unfold globalMarkProduct
          exact Finset.dvd_prod_of_mem (fun g => (marks g).val)
            (Finset.mem_univ g)
        have hpDvdD : p ∣ D := by
          rw [← hEq]
          dsimp [D, assignmentModulus]
          exact dvd_mul_of_dvd_right hpDvdMark _
        exact hDnot hpDvdD
      · have hpR : p ∈ R := by
          change p ∈ P \ globalMarkImage G marks
          exact Finset.mem_sdiff.mpr ⟨hpP, hpMark⟩
        have hpnotA : p ∉ A := by
          rcases hban with hpnotP | hpnotA
          · exact (hpnotP hpP).elim
          · exact hpnotA
        have hallowNot : allow ⟨p, hpR⟩ ≠ true := by
          intro htrue
          apply hpnotA
          unfold A permissionAllowed
          apply Finset.mem_image.mpr
          exact ⟨⟨p, hpR⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, htrue⟩, rfl⟩
        have hnotDiv : ¬ p ∣ u :=
          (hMaskGood ⟨p, hpR⟩).resolve_left hallowNot
        exact hnotDiv
    · intro hpDivU
      rcases hban with hpnotP | hpnotA
      · exact globalAssignmentMask_no_banned_divisor C x jstar u micro marks allow
          hgood.1.2 hMaskGood p hpPrime hpSmall hpDivU hDnotProduct (Or.inl hpnotP)
      · exact globalAssignmentMask_no_banned_divisor C x jstar u micro marks allow
          hgood.1.2 hMaskGood p hpPrime hpSmall hpDivU hDnotProduct (Or.inl hpP)
  have hData := pairSieveData_object_and_good_of_conditions
    ⌈M⌉₊ ⌈2 * M⌉₊ ⌈N⌉₊ ⌈2 * N⌉₊ D (W x) P A Q
    (assignmentModulus_pos C x jstar micro marks) hQprime hQlarge
    m n u hm hn hDdiv hmn hroughM hroughN hnoBanned
  change (m, n) ∈
      (pairSieveData ⌈M⌉₊ ⌈2 * M⌉₊ ⌈N⌉₊ ⌈2 * N⌉₊ D (W x) P A Q
        (assignmentModulus_pos C x jstar micro marks) hQprime).objects ∧
    ∀ p ∈ Q, ¬ (pairSieveData ⌈M⌉₊ ⌈2 * M⌉₊ ⌈N⌉₊ ⌈2 * N⌉₊ D (W x) P A Q
      (assignmentModulus_pos C x jstar micro marks) hQprime).bad p (m, n)
  exact hData

def assignmentPairIndex (z : ℕ × ℕ) : ℕ := (z.1 * z.2 - 1) / 2

def assignmentPairEvent (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (micro : MicroAssignments C x jstar)
    (marks : GlobalMarkChoices (C.bands.groups x))
    (allow : PermissionIndex (assignmentMaskPrimes C x marks) → Bool)
    (z : ℕ × ℕ) : Prop :=
  Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 ∧
    assignmentPrimeLower C x jstar micro marks ∧
    globalAssignmentMaskGood C x jstar (assignmentPairIndex z)
      (micro, ⟨marks, allow⟩) ∧
    permissionMaskGood (assignmentMaskPrimes C x marks)
      (assignmentPairIndex z) allow

theorem assignment_mask_pair_count_le_sifted
    (C : CandidateData) (x M N : ℝ) (hx : 0 ≤ x) (jstar : ℕ)
    (micro : MicroAssignments C x jstar)
    (marks : GlobalMarkChoices (C.bands.groups x))
    (allow : PermissionIndex (assignmentMaskPrimes C x marks) → Bool) :
    let Mbox := (Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊).filter (Analytic.rough (W x))
    let Nbox := (Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊).filter (Analytic.rough (W x))
    let D := assignmentModulus C x jstar micro marks
    let R := assignmentMaskPrimes C x marks
    let S := pairBudgetData C x M N D R
      (assignmentModulus_pos C x jstar micro marks) allow
    (((Mbox.product Nbox).filter (assignmentPairEvent C x jstar micro marks allow)).card : ℝ)
      ≤ S.sifted := by
  classical
  let Mbox := (Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊).filter (Analytic.rough (W x))
  let Nbox := (Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊).filter (Analytic.rough (W x))
  let D := assignmentModulus C x jstar micro marks
  let R := assignmentMaskPrimes C x marks
  let S := pairBudgetData C x M N D R
    (assignmentModulus_pos C x jstar micro marks) allow
  let T := (Mbox.product Nbox).filter (assignmentPairEvent C x jstar micro marks allow)
  have hT : T ⊆ S.objects.filter fun z => ∀ p ∈ S.primes, ¬ S.bad p z := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hpair := Finset.mem_product.mp hz'.1
    have hMrough := (Finset.mem_filter.mp hpair.1).2
    have hNrough := (Finset.mem_filter.mp hpair.2).2
    have hMbox := (Finset.mem_filter.mp hpair.1).1
    have hNbox := (Finset.mem_filter.mp hpair.2).1
    rcases hz'.2 with ⟨hodd, hprod1, hlower, hgood, hmask⟩
    obtain ⟨k, hk⟩ := hodd
    have hmn : z.1 * z.2 = 2 * assignmentPairIndex z + 1 := by
      dsimp [assignmentPairIndex]
      omega
    have hData := assignment_pair_mem_pairBudgetSifted C x M N hx jstar
      micro marks allow (assignmentPairIndex z) z.1 z.2 hprod1 hmn
      hMrough hNrough hMbox hNbox hgood hmask
    exact Finset.mem_filter.mpr ⟨hData.1, hData.2⟩
  have hweight : ∀ z ∈ S.objects, S.weight z = 1 := by
    intro z hz
    rfl
  have hcount := sifted_count_upper_of_subset S hweight T hT
  simpa [T, Mbox, Nbox] using hcount

theorem permissionMaskProbability_nonneg
    (R : Finset ℕ) (q : ℝ) (allow : PermissionIndex R → Bool)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ permissionMaskProbability R q allow := by
  classical
  unfold permissionMaskProbability
  apply Finset.prod_nonneg
  intro p hp
  by_cases hallow : allow p
  · simp [hallow, hq0]
  · simp [hallow]
    linarith

theorem weighted_le_cutoff_mul_bandWeight
    (δ : ℝ) (C : CandidateData) (x : ℝ) (jstar u : ℕ) (B : ℝ)
    (hC : C.Geometry δ) (hPsi : ∀ y, C.psi y ≤ B)
    (hweightNonneg : 0 ≤ C.weighted x jstar u)
    (hweightNe : C.weighted x jstar u ≠ 0) :
    C.weighted x jstar u ≤ B * C.bands.weight x jstar u := by
  rcases hC with ⟨hvalid, hc₁, hc₂, hratio, hs', hδ, hlast, hprefix, hgap,
    hq, hell, ha, hb, hc, hd, hmicro, hlo, hhi, hthetaSmall, hmicroSmall,
    hpsiCont, hpsiSupport, hpsiNonneg, hpsiLower⟩
  have hpsiNonneg' : 0 ≤ C.psi ((u : ℝ) / x) := hpsiNonneg _
  have hpsiNe : C.psi ((u : ℝ) / x) ≠ 0 := by
    intro hzero
    apply hweightNe
    simp [CandidateData.weighted, hzero]
  have hpsiPos : 0 < C.psi ((u : ℝ) / x) := by
    rcases lt_or_eq_of_le hpsiNonneg' with hpos | hzero
    · exact hpos
    · exact (hpsiNe hzero.symm).elim
  have hbaseNonneg : 0 ≤ C.bands.weight x jstar u := by
    by_contra h
    have hneg : C.bands.weight x jstar u < 0 := lt_of_not_ge h
    have hproduct : C.bands.weight x jstar u * C.psi ((u : ℝ) / x) < 0 :=
      mul_neg_of_neg_of_pos hneg hpsiPos
    have hproduct' : 0 ≤ C.bands.weight x jstar u * C.psi ((u : ℝ) / x) := by
      simpa [CandidateData.weighted] using hweightNonneg
    linarith
  calc
    C.weighted x jstar u = C.bands.weight x jstar u * C.psi ((u : ℝ) / x) := rfl
    _ ≤ C.bands.weight x jstar u * B :=
      mul_le_mul_of_nonneg_left (hPsi _) hbaseNonneg
    _ = B * C.bands.weight x jstar u := by ring

theorem assignmentPrimeLower_of_globalGood_of_supported
    (C : CandidateData) (x : ℝ) (jstar : ℕ) (u : ℕ)
    (micro : MicroAssignments C x jstar)
    (marks : GlobalMarkChoices (C.bands.groups x))
    (allow : PermissionIndex (assignmentMaskPrimes C x marks) → Bool)
    (hu : u ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ u → L x ^ (20 : ℕ) ≤ (p : ℝ))
    (hgood : globalAssignmentMaskGood C x jstar u (micro, ⟨marks, allow⟩)) :
    assignmentPrimeLower C x jstar micro marks := by
  intro p hp hpD
  have hDdiv : assignmentModulus C x jstar micro marks ∣ u := by
    dsimp [assignmentModulus]
    exact globalAssignmentMask_divisor_dvd_index (C.bands.groups x) u
      (microAssignmentProduct C x jstar micro) marks hgood.1.1 hgood.2 hu
  exact hsupport p hp (Nat.dvd_trans hpD hDdiv)

theorem globalAssignmentMaskTerm_eq_zero_of_not_primeLower
    (C : CandidateData) (x : ℝ) (jstar u : ℕ)
    (micro : MicroAssignments C x jstar)
    (marks : GlobalMarkChoices (C.bands.groups x))
    (allow : PermissionIndex (assignmentMaskPrimes C x marks) → Bool)
    (hu : u ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ u → L x ^ (20 : ℕ) ≤ (p : ℝ))
    (hgoodLower : ¬ assignmentPrimeLower C x jstar micro marks) :
    globalAssignmentMaskTerm C x jstar u (micro, ⟨marks, allow⟩) = 0 := by
  by_cases hgood : globalAssignmentMaskGood C x jstar u (micro, ⟨marks, allow⟩)
  · have hLower := assignmentPrimeLower_of_globalGood_of_supported C x jstar u
      micro marks allow hu hsupport hgood
    exact (hgoodLower hLower).elim
  · simp [globalAssignmentMaskTerm, hgood]

theorem globalAssignmentMaskTerm_sum_eq_lower
    (C : CandidateData) (x : ℝ) (jstar u : ℕ) (hu : u ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ u → L x ^ (20 : ℕ) ≤ (p : ℝ)) :
    (∑ a : GlobalAssignmentMasks C x jstar,
      globalAssignmentMaskTerm C x jstar u a) =
    ∑ a : GlobalAssignmentMasks C x jstar,
      if assignmentPrimeLower C x jstar a.1 a.2.1 then
        globalAssignmentMaskTerm C x jstar u a else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hLower : assignmentPrimeLower C x jstar a.1 a.2.1
  · simp [hLower]
  · have hz := globalAssignmentMaskTerm_eq_zero_of_not_primeLower C x jstar u
      a.1 a.2.1 a.2.2 hu hsupport hLower
    simp [hLower, hz]

theorem weighted_pair_le_assignmentPairEventSum
    (δ : ℝ) (C : CandidateData) (x : ℝ) (jstar : ℕ) (B : ℝ)
    (hC : C.Geometry δ) (hx : 1 < x)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (hell : C.bands.geometry.ell = 1) (hq : 0 < C.bands.geometry.q)
    (hq0 : 0 ≤ C.bands.geometry.q) (hq1 : C.bands.geometry.q ≤ 1)
    (hB : 0 ≤ B) (hPsi : ∀ y, C.psi y ≤ B)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g)
    (hweightNonneg : ∀ u, 0 ≤ C.weighted x jstar u)
    (hsupport : ∀ u, C.weighted x jstar u ≠ 0 →
      ∀ p : ℕ, p.Prime → p ∣ u → L x ^ (20 : ℕ) ≤ (p : ℝ))
    (z : ℕ × ℕ) :
    (if Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 then
      C.weighted x jstar (assignmentPairIndex z) else 0) ≤
      B * ∑ a : GlobalAssignmentMasks C x jstar,
        if assignmentPairEvent C x jstar a.1 a.2.1 a.2.2 z then
          assignmentCoefficient C x * permissionMaskProbability
            (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2
        else 0 := by
  classical
  by_cases hpair : Odd (z.1 * z.2) ∧ 1 < z.1 * z.2
  · obtain ⟨k, hk⟩ := hpair.1
    have hmn : z.1 * z.2 = 2 * assignmentPairIndex z + 1 := by
      dsimp [assignmentPairIndex]
      omega
    have hu : assignmentPairIndex z ≠ 0 := by
      intro hu0
      rw [hmn, hu0] at hpair
      norm_num at hpair
    by_cases hweight : C.weighted x jstar (assignmentPairIndex z) = 0
    · have hcoeffNonneg (a : GlobalAssignmentMasks C x jstar) :
        0 ≤ assignmentCoefficient C x * permissionMaskProbability
          (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 :=
        mul_nonneg (assignmentCoefficient_nonneg C x)
          (permissionMaskProbability_nonneg _ _ _ hq0 hq1)
      have hsumNonneg : 0 ≤ ∑ a : GlobalAssignmentMasks C x jstar,
          if assignmentPairEvent C x jstar a.1 a.2.1 a.2.2 z then
            assignmentCoefficient C x * permissionMaskProbability
              (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2
          else 0 := by
        apply Finset.sum_nonneg
        intro a ha
        by_cases hevent : assignmentPairEvent C x jstar a.1 a.2.1 a.2.2 z
        · simpa [hevent] using hcoeffNonneg a
        · simp [hevent]
      simp [hpair, hweight]
      exact mul_nonneg hB hsumNonneg
    · have hcut := weighted_le_cutoff_mul_bandWeight δ C x jstar
        (assignmentPairIndex z) B hC hPsi (hweightNonneg _) hweight
      have hmajorant := bandWeight_le_global_assignment_mask_sum C δ x jstar
        (assignmentPairIndex z) hC (by linarith) hbound hj hu hell hq hmass
      have hsupportU : ∀ p : ℕ, p.Prime → p ∣ assignmentPairIndex z →
          L x ^ (20 : ℕ) ≤ (p : ℝ) := hsupport _ hweight
      have hsumLower := globalAssignmentMaskTerm_sum_eq_lower C x jstar
        (assignmentPairIndex z) hu hsupportU
      have hsumEvent :
          (∑ a : GlobalAssignmentMasks C x jstar,
            if assignmentPrimeLower C x jstar a.1 a.2.1 then
              globalAssignmentMaskTerm C x jstar (assignmentPairIndex z) a else 0) =
          ∑ a : GlobalAssignmentMasks C x jstar,
            if assignmentPairEvent C x jstar a.1 a.2.1 a.2.2 z then
              assignmentCoefficient C x * permissionMaskProbability
                (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2
            else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hLower : assignmentPrimeLower C x jstar a.1 a.2.1
        · simp [assignmentPairEvent, hpair, hLower, assignmentCoefficient,
            markBaseCoefficient, assignmentMaskPrimes,
            globalAssignmentMaskTerm_eq_probability_indicator]
        · simp [assignmentPairEvent, hpair, hLower]
      simp only [hpair]
      calc
        C.weighted x jstar (assignmentPairIndex z) ≤
            B * C.bands.weight x jstar (assignmentPairIndex z) := hcut
        _ ≤ B * ∑ a : GlobalAssignmentMasks C x jstar,
              globalAssignmentMaskTerm C x jstar (assignmentPairIndex z) a :=
          mul_le_mul_of_nonneg_left hmajorant hB
        _ = B * ∑ a : GlobalAssignmentMasks C x jstar,
              if assignmentPrimeLower C x jstar a.1 a.2.1 then
                globalAssignmentMaskTerm C x jstar (assignmentPairIndex z) a else 0 := by
          rw [← hsumLower]
        _ = B * ∑ a : GlobalAssignmentMasks C x jstar,
              if assignmentPairEvent C x jstar a.1 a.2.1 a.2.2 z then
                assignmentCoefficient C x * permissionMaskProbability
                  (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2
              else 0 := by rw [hsumEvent]
  · have hnoEvent : ∀ a : GlobalAssignmentMasks C x jstar,
        ¬ assignmentPairEvent C x jstar a.1 a.2.1 a.2.2 z := by
      intro a hevent
      exact hpair ⟨hevent.1, hevent.2.1⟩
    simp [hpair, hnoEvent]

theorem balancedRoughSum_le_assignmentSiftedSum_of_pointwise
    (δ : ℝ) (C : CandidateData) (x M N : ℝ) (jstar : ℕ) (B : ℝ)
    (hC : C.Geometry δ) (hx : 1 < x)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (hell : C.bands.geometry.ell = 1) (hq : 0 < C.bands.geometry.q)
    (hq0 : 0 ≤ C.bands.geometry.q) (hq1 : C.bands.geometry.q ≤ 1)
    (hB : 0 ≤ B) (hPsi : ∀ y, C.psi y ≤ B)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g)
    (hweightNonneg : ∀ u, 0 ≤ C.weighted x jstar u)
    (hsupport : ∀ u, C.weighted x jstar u ≠ 0 →
      ∀ p : ℕ, p.Prime → p ∣ u → L x ^ (20 : ℕ) ≤ (p : ℝ)) :
    balancedRoughSum C x M N jstar ≤ B * assignmentSiftedSum C x M N jstar := by
  classical
  let Mbox := (Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊).filter (Analytic.rough (W x))
  let Nbox := (Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊).filter (Analytic.rough (W x))
  let Pairs := Mbox.product Nbox
  let A := GlobalAssignmentMasks C x jstar
  let pairTerm : ℕ × ℕ → ℝ := fun z =>
    if Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 then
      C.weighted x jstar (assignmentPairIndex z) else 0
  let pairEventTerm : (ℕ × ℕ) → A → ℝ := fun z a =>
    if assignmentPairEvent C x jstar a.1 a.2.1 a.2.2 z then
      assignmentCoefficient C x * permissionMaskProbability
        (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 else 0
  have hpairRewrite : balancedRoughSum C x M N jstar =
      ∑ z ∈ Pairs, pairTerm z := by
    simp only [balancedRoughSum, Pairs, Mbox, Nbox, pairTerm]
    exact (Finset.sum_product _ _ (fun z : ℕ × ℕ =>
      if Odd (z.1 * z.2) ∧ 1 < z.1 * z.2 then
        C.weighted x jstar (assignmentPairIndex z) else 0)).symm
  have hpoint (z : ℕ × ℕ) (hz : z ∈ Pairs) :
      pairTerm z ≤ B * ∑ a : A, pairEventTerm z a := by
    simpa [pairTerm, pairEventTerm, A] using
      weighted_pair_le_assignmentPairEventSum δ C x jstar B hC hx hbound hj
        hell hq hq0 hq1 hB hPsi hmass hweightNonneg hsupport z
  have hsumPoint :
      (∑ z ∈ Pairs, pairTerm z) ≤
        ∑ z ∈ Pairs, B * ∑ a : A, pairEventTerm z a := by
    apply Finset.sum_le_sum
    intro z hz
    exact hpoint z hz
  have hswap :
      (∑ z ∈ Pairs, ∑ a : A, pairEventTerm z a) =
        ∑ a : A, ∑ z ∈ Pairs, pairEventTerm z a := by
    exact Finset.sum_comm
  have hcountEq (a : A) :
      (∑ z ∈ Pairs, pairEventTerm z a) =
        assignmentCoefficient C x * permissionMaskProbability
          (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 *
          (((Pairs.filter (fun z => assignmentPairEvent C x jstar
            a.1 a.2.1 a.2.2 z)).card : ℝ)) := by
    dsimp [pairEventTerm]
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  have hcardBound (a : A) :
      (((Pairs.filter (fun z => assignmentPairEvent C x jstar
        a.1 a.2.1 a.2.2 z)).card : ℝ)) ≤
      if assignmentPrimeLower C x jstar a.1 a.2.1 then
        (pairBudgetData C x M N (assignmentModulus C x jstar a.1 a.2.1)
          (assignmentMaskPrimes C x a.2.1)
          (assignmentModulus_pos C x jstar a.1 a.2.1) a.2.2).sifted
      else 0 := by
    by_cases hLower : assignmentPrimeLower C x jstar a.1 a.2.1
    · simpa [Pairs, Mbox, Nbox, A, hLower] using
        (assignment_mask_pair_count_le_sifted C x M N (by linarith) jstar
          a.1 a.2.1 a.2.2)
    · have hEmpty : Pairs.filter (fun z => assignmentPairEvent C x jstar
          a.1 a.2.1 a.2.2 z) = ∅ := by
        ext z
        simp [assignmentPairEvent, hLower]
      simp [hLower, hEmpty]
  have hcoeffNonneg (a : A) :
      0 ≤ assignmentCoefficient C x * permissionMaskProbability
        (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 :=
    mul_nonneg (assignmentCoefficient_nonneg C x)
      (permissionMaskProbability_nonneg _ _ _ hq0 hq1)
  have hsumCount :
      (∑ a : A,
        assignmentCoefficient C x * permissionMaskProbability
          (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 *
          (((Pairs.filter (fun z => assignmentPairEvent C x jstar
            a.1 a.2.1 a.2.2 z)).card : ℝ))) ≤
      ∑ a : A,
        if assignmentPrimeLower C x jstar a.1 a.2.1 then
          assignmentCoefficient C x * permissionMaskProbability
            (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 *
            (pairBudgetData C x M N (assignmentModulus C x jstar a.1 a.2.1)
              (assignmentMaskPrimes C x a.2.1)
              (assignmentModulus_pos C x jstar a.1 a.2.1) a.2.2).sifted
        else 0 := by
    apply Finset.sum_le_sum
    intro a ha
    have hcard := hcardBound a
    have hterm := mul_le_mul_of_nonneg_left hcard (hcoeffNonneg a)
    by_cases hLower : assignmentPrimeLower C x jstar a.1 a.2.1
    · simpa [hLower] using hterm
    · simpa [hLower] using hterm
  have hsumTarget :
      (∑ a : A,
        if assignmentPrimeLower C x jstar a.1 a.2.1 then
          assignmentCoefficient C x * permissionMaskProbability
            (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 *
            (pairBudgetData C x M N (assignmentModulus C x jstar a.1 a.2.1)
              (assignmentMaskPrimes C x a.2.1)
              (assignmentModulus_pos C x jstar a.1 a.2.1) a.2.2).sifted
        else 0) = assignmentSiftedSum C x M N jstar := by
    dsimp [A]
    simp only [GlobalAssignmentMasks, GlobalMarkMasks, assignmentMaskPrimes,
      Fintype.sum_prod_type, Fintype.sum_sigma]
    unfold assignmentSiftedSum assignmentSiftedAverage
    apply Finset.sum_congr rfl
    intro micro hmicro
    apply Finset.sum_congr rfl
    intro marks hmarks
    by_cases hLower : assignmentPrimeLower C x jstar micro marks
    · simp only [if_pos hLower, mul_assoc]
      rw [← Finset.mul_sum]
      rfl
    · simp [hLower]
  calc
    balancedRoughSum C x M N jstar = ∑ z ∈ Pairs, pairTerm z := hpairRewrite
    _ ≤ ∑ z ∈ Pairs, B * ∑ a : A, pairEventTerm z a := hsumPoint
    _ = B * ∑ z ∈ Pairs, ∑ a : A, pairEventTerm z a := by
      rw [Finset.mul_sum]
    _ = B * ∑ a : A, ∑ z ∈ Pairs, pairEventTerm z a := by
      rw [hswap]
    _ = B * ∑ a : A,
        assignmentCoefficient C x * permissionMaskProbability
          (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 *
          (((Pairs.filter (fun z => assignmentPairEvent C x jstar
            a.1 a.2.1 a.2.2 z)).card : ℝ)) := by
      apply congrArg (fun t : ℝ => B * t)
      exact Finset.sum_congr rfl (by
        intro a ha
        exact hcountEq a)
    _ ≤ B * ∑ a : A,
        if assignmentPrimeLower C x jstar a.1 a.2.1 then
          assignmentCoefficient C x * permissionMaskProbability
            (assignmentMaskPrimes C x a.2.1) C.bands.geometry.q a.2.2 *
            (pairBudgetData C x M N (assignmentModulus C x jstar a.1 a.2.1)
              (assignmentMaskPrimes C x a.2.1)
              (assignmentModulus_pos C x jstar a.1 a.2.1) a.2.2).sifted
        else 0 := mul_le_mul_of_nonneg_left hsumCount hB
    _ = B * assignmentSiftedSum C x M N jstar := by rw [hsumTarget]

theorem AssignmentSiftedBridgeTask_proof : AssignmentSiftedBridgeTask := by
  intro δ C hC hBounds
  obtain ⟨B, hB, hPsi⟩ := candidate_psi_uniform_bound δ C hC
  refine ⟨B, hB, ?_⟩
  intro jstar hj
  have hCcopy := hC
  rcases hCcopy with ⟨hvalid, hc₁, hc₂, hratio, hs', hδ, hlastGeometry,
    hprefix, hgap, hqEq, hell, ha, hb, hc, hd, hmicro, hthetaLo, hthetaHi,
    hthetaSmall, hmicroSmall, hpsiCont, hpsiSupport, hpsiNonneg, hpsiLower⟩
  rcases hvalid with ⟨hr₀, hb₁, hb₂, hsValid, hratioValid, hgapValid,
    hscaleValid, hlastTendsto, hvalidTailData⟩
  rcases hvalidTailData with ⟨cmin, cmax, hcmin, hcmax, hvalidTail⟩
  have hAdmissible : ∀ᶠ x : ℝ in atTop,
      Analytic.Admissible C.bands.geometry x (C.bands.groups x) := by
    filter_upwards [hvalidTail] with x hx
    exact hx.1
  have hlastLarge : ∀ᶠ x : ℝ in atTop, C.micro ≤ C.bands.last x :=
    hlastTendsto.eventually (eventually_ge_atTop C.micro)
  obtain ⟨K, CA, cmin', cmax', hK, hcmin', hcmax', hBoundsEvent⟩ := hBounds
  filter_upwards [hBoundsEvent jstar hj, hAdmissible, hlastLarge,
    eventually_gt_atTop (1 : ℝ)] with x hBoundsX hAdm hlastX hx
  have hmassBounds := hAdm.2.2.1
  have hmass : ∀ g, 0 < mass (C.bands.groups x) g := by
    rcases C.bands.geometry.positive with ⟨_, _, hvmin, _⟩
    intro g
    exact lt_of_lt_of_le hvmin (hmassBounds g).1
  have hbound : C.micro ≤ C.bands.last x + 1 := by omega
  have hq : 0 < C.bands.geometry.q := by rw [hqEq]; norm_num
  have hq0 : 0 ≤ C.bands.geometry.q := by rw [hqEq]; norm_num
  have hq1 : C.bands.geometry.q ≤ 1 := by rw [hqEq]; norm_num
  have hweightNonneg : ∀ u, 0 ≤ C.weighted x jstar u := hBoundsX.2.2.2.1
  have hsupport : ∀ u, C.weighted x jstar u ≠ 0 →
      ∀ p : ℕ, p.Prime → p ∣ u → L x ^ (20 : ℕ) ≤ (p : ℝ) := by
    intro u hweight p hp hpdiv
    exact ((hBoundsX.2.2.2.2.2 u hweight).2.2 p hp hpdiv).1
  intro M N
  exact balancedRoughSum_le_assignmentSiftedSum_of_pointwise δ C x M N jstar B
    hC hx hbound (hmicro.trans hj) hell (by simpa [hqEq] using hq)
    hq0 hq1 hB.le hPsi hmass hweightNonneg hsupport


end Erdos821.S56Core
