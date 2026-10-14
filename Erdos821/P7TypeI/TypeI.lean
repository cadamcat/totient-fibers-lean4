import Erdos821.Blueprint.Candidate
import Erdos821.S56.WeightBound

/-! Initial P7 Type I lemmas. -/
noncomputable section
open scoped BigOperators
open Filter Erdos821.Blueprint.Analytic

namespace Erdos821.P7B

open Erdos821.Blueprint

def firstSlot (D : BandData) (x : ℝ) (hr₀ : 1 ≤ D.r₀) : D.Slot x :=
  (⟨0, Nat.zero_lt_succ _⟩, ⟨0, by omega⟩)

abbrev RestLists (D : BandData) (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x) :=
  ∀ s : {s : D.Slot x // s ≠ s₀}, D.SlotValue x jstar s.1

def restProduct (D : BandData) (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x)
    (z : RestLists D x jstar s₀) : ℕ :=
  ∏ s, (z s).val

def splitListsEquiv (D : BandData) (x : ℝ) (jstar : ℕ) (s₀ : D.Slot x) :
    D.Lists x jstar ≃ D.SlotValue x jstar s₀ × RestLists D x jstar s₀ :=
  Equiv.piSplitAt s₀ (fun s => D.SlotValue x jstar s)

theorem listProduct_split (D : BandData) (x : ℝ) (jstar : ℕ)
    (s₀ : D.Slot x) (p : D.SlotValue x jstar s₀)
    (z : RestLists D x jstar s₀) :
    D.listProduct ((splitListsEquiv D x jstar s₀).symm (p, z)) =
      p.val * restProduct D x jstar s₀ z := by
  classical
  unfold BandData.listProduct restProduct
  have hrest :
      (∏ s ∈ Finset.univ.erase s₀,
        ((splitListsEquiv D x jstar s₀).symm (p, z) s).val) =
        ∏ s : {s : D.Slot x // s ≠ s₀}, (z s).val := by
    rw [Finset.prod_subtype (p := fun s : D.Slot x => s ≠ s₀)
      (Finset.univ.erase s₀) (by intro s; simp)
      (fun s => ((splitListsEquiv D x jstar s₀).symm (p, z) s).val)]
    refine Fintype.prod_congr _ _ ?_
    intro s
    simp [splitListsEquiv, Equiv.piSplitAt, s.2]
  have hslot : ((splitListsEquiv D x jstar s₀).symm (p, z) s₀).val = p.val := by
    simp [splitListsEquiv, Equiv.piSplitAt]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (D.Slot x))
    (fun s => ((splitListsEquiv D x jstar s₀).symm (p, z) s).val)
    (Finset.mem_univ s₀), hrest, hslot]

def listFiberSigmaEquiv (D : BandData) (x : ℝ) (jstar : ℕ)
    (s₀ : D.Slot x) (v : ℕ) :
    {z : D.Lists x jstar // D.listProduct z = v} ≃
      Σ p : D.SlotValue x jstar s₀,
        {z : RestLists D x jstar s₀ // p.val * restProduct D x jstar s₀ z = v} := by
  classical
  let e := splitListsEquiv D x jstar s₀
  let pairFiber : Type :=
    {q : D.SlotValue x jstar s₀ × RestLists D x jstar s₀ //
      q.1.val * restProduct D x jstar s₀ q.2 = v}
  let eFiber : {z : D.Lists x jstar // D.listProduct z = v} ≃ pairFiber := {
    toFun := fun z => ⟨e z.1, by
      calc
        (e z.1).1.val * restProduct D x jstar s₀ (e z.1).2 =
            D.listProduct (e.symm (e z.1)) := (listProduct_split D x jstar s₀ _ _).symm
        _ = v := by rw [e.symm_apply_apply]; exact z.2⟩
    invFun := fun q => ⟨e.symm q.1, by
      calc
        D.listProduct (e.symm q.1) =
            q.1.1.val * restProduct D x jstar s₀ q.1.2 := listProduct_split D x jstar s₀ _ _
        _ = v := q.2⟩
    left_inv := by
      intro z
      apply Subtype.ext
      exact e.left_inv z.1
    right_inv := by
      intro q
      apply Subtype.ext
      exact e.apply_symm_apply q.1 }
  exact eFiber.trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun (p : D.SlotValue x jstar s₀) (z : RestLists D x jstar s₀) =>
        p.val * restProduct D x jstar s₀ z = v))

theorem listFiber_card_eq (D : BandData) (x : ℝ) (jstar : ℕ)
    (s₀ : D.Slot x) (v : ℕ) :
    Fintype.card {z : D.Lists x jstar // D.listProduct z = v} =
      ∑ p : D.SlotValue x jstar s₀,
        Fintype.card {z : RestLists D x jstar s₀ // p.val * restProduct D x jstar s₀ z = v} := by
  classical
  calc
    _ = Fintype.card (Σ p : D.SlotValue x jstar s₀,
          {z : RestLists D x jstar s₀ // p.val * restProduct D x jstar s₀ z = v}) :=
        Fintype.card_congr (listFiberSigmaEquiv D x jstar s₀ v)
    _ = _ := Fintype.card_sigma

theorem aQ_eq_fiber_card (D : BandData) (x : ℝ) (jstar v : ℕ) :
    D.aQ x jstar v =
      ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ *
        (Fintype.card {z : D.Lists x jstar // D.listProduct z = v} : ℝ) := by
  unfold BandData.aQ
  congr 1
  exact_mod_cast (Fintype.card_of_subtype
    (Finset.univ.filter (fun z : D.Lists x jstar => D.listProduct z = v))
    (by intro z; simp)).symm

theorem aQ_eq_slotFiber_sum (D : BandData) (x : ℝ) (jstar v : ℕ)
    (s₀ : D.Slot x) :
    D.aQ x jstar v =
      ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ *
        ∑ p : D.SlotValue x jstar s₀,
          (Fintype.card
            {z : RestLists D x jstar s₀ // p.val * restProduct D x jstar s₀ z = v} : ℝ) := by
  rw [aQ_eq_fiber_card D x jstar v, listFiber_card_eq D x jstar s₀ v]
  simp only [Nat.cast_sum]

theorem candidate_aQ_divisor_bound (C : CandidateData) (δ : ℝ)
    (hC : C.Geometry δ) (jstar : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ v : ℕ,
      C.bands.aQ x jstar v ≤ (v.divisors.card : ℝ) :=
  Erdos821.P6Slot.slotMultiplicityTask_proof C.bands hC.1 jstar

theorem candidate_band_weight_divisor_bound (C : CandidateData) (δ : ℝ)
    (hC : C.Geometry δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop,
      ∀ u : ℕ, 0 < u →
        C.bands.weight x jstar u ≤ L x ^ A * (u.divisors.card : ℝ) :=
  Erdos821.S56Core.band_weight_divisor_bound C.bands hC.1

theorem candidate_psi_bounds (C : CandidateData) (δ : ℝ)
    (hC : C.Geometry δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 ≤ C.psi y ∧ C.psi y ≤ M := by
  rcases hC with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hψ, hsupp, hnonneg, _⟩
  have hcont : Continuous C.psi := hψ.continuous
  have hcompact : IsCompact (C.psi '' Set.Icc (1 : ℝ) 2) :=
    isCompact_Icc.image_of_continuousOn hcont.continuousOn
  obtain ⟨M, hM⟩ := hcompact.bddAbove
  have hM0 : 0 ≤ M := by
    have h1 : (1 : ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
    exact (hnonneg 1).trans (hM ⟨1, h1, rfl⟩)
  refine ⟨M, hM0, ?_⟩
  intro y
  have hnonnegY := hnonneg y
  by_cases hy : y ∈ Set.Icc (1 : ℝ) 2
  · exact ⟨hnonnegY, hM ⟨y, hy, rfl⟩⟩
  · have hnotSupport : y ∉ Function.support C.psi := fun hySupport => hy (hsupp hySupport)
    have hzero : C.psi y = 0 := by
      by_contra hyzero
      exact hnotSupport (by simpa [Function.support] using hyzero)
    simpa [hzero] using hM0

theorem candidate_weight_divisor_bound (C : CandidateData) (δ : ℝ)
    (hC : C.Geometry δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop,
      ∀ u : ℕ, 0 < u →
        C.weighted x jstar u ≤ L x ^ K * (u.divisors.card : ℝ) := by
  obtain ⟨A, hA, hBand⟩ := candidate_band_weight_divisor_bound C δ hC
  obtain ⟨M, hM, hψ⟩ := candidate_psi_bounds C δ hC
  refine ⟨A + 1, by linarith, ?_⟩
  intro jstar
  filter_upwards [hBand jstar,
    Erdos821.S56Core.tendsto_L.eventually (eventually_ge_atTop M),
    Erdos821.S56Core.tendsto_L.eventually (eventually_gt_atTop 0)] with x hBand hMx hLpos
  intro u hu
  have hW0 : 0 ≤ C.bands.weight x jstar u :=
    Erdos821.S56Core.band_weight_nonneg C.bands x jstar u
  calc
    C.weighted x jstar u = C.bands.weight x jstar u * C.psi ((u : ℝ) / x) := rfl
    _ ≤ C.bands.weight x jstar u * M :=
      mul_le_mul_of_nonneg_left (hψ ((u : ℝ) / x)).2 hW0
    _ ≤ (L x ^ A * (u.divisors.card : ℝ)) * M :=
      mul_le_mul_of_nonneg_right (hBand u hu) hM
    _ = (L x ^ A * M) * (u.divisors.card : ℝ) := by ring
    _ ≤ (L x ^ A * L x) * (u.divisors.card : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left hMx (Real.rpow_nonneg (le_of_lt hLpos) _)
    _ = L x ^ (A + 1) * (u.divisors.card : ℝ) := by
      rw [Real.rpow_add hLpos A 1, Real.rpow_one]

theorem firstSlot_is_pure (D : BandData) (x : ℝ) (jstar : ℕ)
    (hr₀ : 1 ≤ D.r₀) (hjstar : 0 < jstar) :
    D.slotValues x jstar (firstSlot D x hr₀) = D.band x 0 := by
  have hzero : (0 : ℕ) ≠ jstar := by omega
  simp [BandData.slotValues, firstSlot, hzero]

theorem coprime_of_dvd_two_mul_add_one {d u : ℕ} (h : d ∣ 2 * u + 1) :
    Nat.Coprime u d := by
  apply Nat.coprime_of_dvd'
  intro p hp hpu hpd
  have hpN : p ∣ 2 * u + 1 := dvd_trans hpd h
  have hp2u : p ∣ 2 * u := hpu.mul_left 2
  have hp1 : p ∣ 1 := by
    simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hpN hp2u
  exact (hp.not_dvd_one hp1).elim

def coprimeMass (C : CandidateData) (x : ℝ) (jstar d : ℕ) : ℝ :=
  ∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => Nat.Coprime u d),
    C.weighted x jstar u

def nonCoprimeMass (C : CandidateData) (x : ℝ) (jstar d : ℕ) : ℝ :=
  ∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => ¬ Nat.Coprime u d),
    C.weighted x jstar u

theorem candidate_mass_coprime_split (C : CandidateData) (x : ℝ)
    (jstar d : ℕ) :
    C.mass x jstar = coprimeMass C x jstar d + nonCoprimeMass C x jstar d := by
  unfold CandidateData.mass coprimeMass nonCoprimeMass
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 ⌊2 * x⌋₊) (fun u : ℕ => Nat.Coprime u d)
    (fun u : ℕ => C.weighted x jstar u)]

theorem candidate_remainder_principal_split (C : CandidateData) (x : ℝ)
    (jstar d : ℕ) :
    C.remainder x jstar d +
        nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) =
      (∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
        C.weighted x jstar u) - coprimeMass C x jstar d / (Nat.totient d : ℝ) := by
  unfold CandidateData.remainder
  rw [candidate_mass_coprime_split]
  ring

def squarefreeModuli (y : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊y⌋₊).filter Squarefree

def reciprocalTotientSquarefreeSum (y : ℝ) : ℝ :=
  ∑ d ∈ squarefreeModuli y, (d.totient : ℝ)⁻¹

def squarefreeModuliDivisibleBy (y : ℝ) (p : ℕ) : Finset ℕ :=
  (squarefreeModuli y).filter (fun d => p ∣ d)

def badSquarefreeReciprocalTotientSum (y : ℝ) (u : ℕ) : ℝ :=
  ∑ d ∈ squarefreeModuli y,
    if Nat.Coprime u d then 0 else (d.totient : ℝ)⁻¹

theorem reciprocalTotientSquarefreeSum_le_inv_sieveProduct (y : ℝ) :
    reciprocalTotientSquarefreeSum y ≤ (sieveProduct y)⁻¹ := by
  classical
  let D := squarefreeModuli y
  let P := primesUpTo y
  have hFactorSubset (d : ℕ) (hd : d ∈ D) : d.primeFactors ⊆ P := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdpos : 0 < d := by
      have hdmem := (Finset.mem_filter.mp hd).1
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hpLe : p ≤ d := Nat.le_of_dvd hdpos hpd
    have hdLe : d ≤ ⌊y⌋₊ := (Finset.mem_Icc.mp ((Finset.mem_filter.mp hd).1)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpPrime.pos, hpLe.trans hdLe⟩, hpPrime⟩
  have hFactorInj : Set.InjOn (fun d : ℕ => d.primeFactors) D := by
    intro d hd e he hde
    have hprodD := Nat.prod_primeFactors_of_squarefree ((Finset.mem_filter.mp hd).2)
    have hprodE := Nat.prod_primeFactors_of_squarefree ((Finset.mem_filter.mp he).2)
    change d.primeFactors = e.primeFactors at hde
    calc
      d = ∏ p ∈ d.primeFactors, p := hprodD.symm
      _ = ∏ p ∈ e.primeFactors, p := by rw [hde]
      _ = e := hprodE
  have hTotientProduct (d : ℕ) (hd : d ∈ D) :
      (d.totient : ℝ)⁻¹ = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1)⁻¹ := by
    have hprod := Nat.prod_primeFactors_of_squarefree ((Finset.mem_filter.mp hd).2)
    have htot := Nat.totient_mul_prod_primeFactors d
    rw [hprod] at htot
    have htot' : d * d.totient = d * ∏ p ∈ d.primeFactors, (p - 1) := by
      simpa only [Nat.mul_comm] using htot
    have htotNat : d.totient = ∏ p ∈ d.primeFactors, (p - 1) :=
      Nat.mul_left_cancel (by
        have hdpos : 0 < d := by
          have hdmem := (Finset.mem_filter.mp hd).1
          exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1
        exact hdpos) htot'
    have htotReal : (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
      calc
        (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p - 1 : ℕ) : ℝ) := by
          exact_mod_cast htotNat
        _ = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
          simpa using (Nat.cast_sub hpPrime.one_le :
            ((p - 1 : ℕ) : ℝ) = (p : ℝ) - (1 : ℕ))
    rw [htotReal, Finset.prod_inv_distrib]
  calc
    reciprocalTotientSquarefreeSum y =
        ∑ d ∈ D, ∏ p ∈ d.primeFactors, ((p : ℝ) - 1)⁻¹ := by
          apply Finset.sum_congr rfl
          intro d hd
          exact hTotientProduct d hd
    _ = ∑ s ∈ D.image (fun d : ℕ => d.primeFactors),
          ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by
          rw [Finset.sum_image hFactorInj]
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.image_subset_iff.mpr (by
              intro d hd
              exact Finset.mem_powerset.mpr (hFactorSubset d hd)))
          intro s hs hnot
          apply Finset.prod_nonneg
          intro p hp
          have hpP : p ∈ P := (Finset.mem_powerset.mp hs) hp
          have hpPrime := (Finset.mem_filter.mp hpP).2
          have hpCast : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
          have hden : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
          exact inv_nonneg.mpr hden
    _ = ∏ p ∈ P, (1 + ((p : ℝ) - 1)⁻¹) := by
          exact (Finset.prod_one_add (s := P)
            (f := fun p : ℕ => ((p : ℝ) - 1)⁻¹)).symm
    _ = (sieveProduct y)⁻¹ := by
          rw [Finset.prod_congr rfl]
          · rw [Finset.prod_inv_distrib]
            rfl
          · intro p hp
            have hpPrime := (Finset.mem_filter.mp hp).2
            have hpTwo : 2 ≤ p := hpPrime.two_le
            have hpReal : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
            have hne : (p : ℝ) - 1 ≠ 0 := by linarith
            have hpne : (p : ℝ) ≠ 0 := by positivity
            field_simp
            ring

theorem reciprocalTotientSquarefreeSum_eventually_le_log
    (hc : ClassicalInputs) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ y : ℝ in atTop,
      reciprocalTotientSquarefreeSum y ≤ K * Real.log y := by
  let c := Real.exp (-Real.eulerMascheroniConstant) / 2
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hclt : c < Real.exp (-Real.eulerMascheroniConstant) := by
    dsimp [c]
    have he := Real.exp_pos (-Real.eulerMascheroniConstant)
    linarith
  have hMertens := hc.mertens.2.eventually (Ioi_mem_nhds hclt)
  refine ⟨c⁻¹, inv_pos.mpr hcpos, ?_⟩
  filter_upwards [hMertens, eventually_gt_atTop (1 : ℝ)] with y hM hyle
  have hylog : 0 < Real.log y := Real.log_pos hyle
  have hprod : 0 < sieveProduct y := by
    have hmul : 0 < Real.log y * sieveProduct y := lt_trans hcpos hM
    rcases (mul_pos_iff.mp hmul) with ⟨_, hP⟩ | ⟨hneg, _⟩
    · exact hP
    · linarith
  have hinv : (sieveProduct y)⁻¹ ≤ Real.log y / c := by
    apply (le_div_iff₀ hcpos).2
    calc
      (sieveProduct y)⁻¹ * c = c * (sieveProduct y)⁻¹ := by ring
      _ ≤ (Real.log y * sieveProduct y) * (sieveProduct y)⁻¹ :=
        mul_le_mul_of_nonneg_right hM.le (inv_nonneg.mpr hprod.le)
      _ = Real.log y := by field_simp [ne_of_gt hprod]
  calc
    reciprocalTotientSquarefreeSum y ≤ (sieveProduct y)⁻¹ :=
      reciprocalTotientSquarefreeSum_le_inv_sieveProduct y
    _ ≤ Real.log y / c := hinv
    _ = c⁻¹ * Real.log y := by ring

theorem reciprocalTotientSquarefreeDivisibleBy_le
    (y : ℝ) (p : ℕ) (hp : p.Prime) :
    (∑ d ∈ squarefreeModuliDivisibleBy y p, (d.totient : ℝ)⁻¹) ≤
      ((p : ℝ) - 1)⁻¹ * reciprocalTotientSquarefreeSum y := by
  classical
  let D := squarefreeModuli y
  let Dp := squarefreeModuliDivisibleBy y p
  have hquotMem (d : ℕ) (hd : d ∈ Dp) : d / p ∈ D := by
    have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
    have hpd : p ∣ d := (Finset.mem_filter.mp hd).2
    have hdpos : 0 < d := by
      have hdmem := (Finset.mem_filter.mp hdD).1
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1
    have hde : p * (d / p) = d := Nat.mul_div_cancel' hpd
    have hepos : 0 < d / p := by
      by_contra h
      cases he : d / p with
      | zero =>
          rw [he] at hde
          simp at hde
          exact hdpos.ne' hde.symm
      | succ n =>
          apply h
          rw [he]
          exact Nat.zero_lt_succ n
    have hdle : d ≤ ⌊y⌋₊ :=
      (Finset.mem_Icc.mp ((Finset.mem_filter.mp hdD).1)).2
    have heSq : Squarefree (d / p) :=
      (Finset.mem_filter.mp hdD).2 |>.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr hepos.ne', (Nat.div_le_self d p).trans hdle⟩, heSq⟩
  have hquotInj : Set.InjOn (fun d : ℕ => d / p) Dp := by
    intro d hd e he hde
    have hpd := (Finset.mem_filter.mp hd).2
    have hpe := (Finset.mem_filter.mp he).2
    change d / p = e / p at hde
    calc
      d = p * (d / p) := (Nat.mul_div_cancel' hpd).symm
      _ = p * (e / p) := by rw [hde]
      _ = e := Nat.mul_div_cancel' hpe
  have hterm (d : ℕ) (hd : d ∈ Dp) :
      (d.totient : ℝ)⁻¹ = ((p : ℝ) - 1)⁻¹ * ((d / p).totient : ℝ)⁻¹ := by
    have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
    have hsqD : Squarefree d := (Finset.mem_filter.mp hdD).2
    have hpd : p ∣ d := (Finset.mem_filter.mp hd).2
    have hde : p * (d / p) = d := Nat.mul_div_cancel' hpd
    have hpnot : ¬ p ∣ d / p := by
      intro hpe
      have hpp : p * p ∣ d := by
        rw [← hde]
        exact Nat.mul_dvd_mul_left p hpe
      exact (Nat.squarefree_iff_prime_squarefree.mp hsqD p hp) hpp
    have htotNat : d.totient = (p - 1) * (d / p).totient := by
      calc
        d.totient = (p * (d / p)).totient := by rw [hde]
        _ = (p - 1) * (d / p).totient :=
          Nat.totient_mul_of_prime_of_not_dvd hp hpnot
    have htotCast : (d.totient : ℝ) =
        ((p - 1 : ℕ) : ℝ) * ((d / p).totient : ℝ) := by
      exact_mod_cast htotNat
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      simpa using (Nat.cast_sub hp.one_le : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - (1 : ℕ))
    rw [hcast] at htotCast
    rw [htotCast, mul_inv]
  have hpFactor : 0 ≤ ((p : ℝ) - 1)⁻¹ := by
    have hpCast : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    exact inv_nonneg.mpr (le_trans (by norm_num) hpCast)
  calc
    (∑ d ∈ Dp, (d.totient : ℝ)⁻¹) =
        ∑ d ∈ Dp, ((p : ℝ) - 1)⁻¹ * ((d / p).totient : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro d hd
          exact hterm d hd
    _ = ((p : ℝ) - 1)⁻¹ * ∑ d ∈ Dp, ((d / p).totient : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
    _ = ((p : ℝ) - 1)⁻¹ *
          ∑ e ∈ Dp.image (fun d : ℕ => d / p), (e.totient : ℝ)⁻¹ := by
          congr 1
          rw [Finset.sum_image hquotInj]
    _ ≤ ((p : ℝ) - 1)⁻¹ * ∑ e ∈ D, (e.totient : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ hpFactor
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.image_subset_iff.mpr hquotMem)
          intro e he hnot
          positivity
    _ = ((p : ℝ) - 1)⁻¹ * reciprocalTotientSquarefreeSum y := by
          rfl

theorem badSquarefreeReciprocalTotientSum_le_primeFactors
    (y : ℝ) (u : ℕ) (hu : 0 < u) :
    badSquarefreeReciprocalTotientSum y u ≤
      reciprocalTotientSquarefreeSum y *
        ∑ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹ := by
  classical
  let D := squarefreeModuli y
  have hPoint (d : ℕ) (hd : d ∈ D) :
      (if Nat.Coprime u d then 0 else (d.totient : ℝ)⁻¹) ≤
        ∑ p ∈ u.primeFactors, if p ∣ d then (d.totient : ℝ)⁻¹ else 0 := by
    by_cases hcop : Nat.Coprime u d
    · rw [if_pos hcop]
      apply Finset.sum_nonneg
      intro p hp
      split_ifs <;> positivity
    · have hcommon : ∃ p ∈ u.primeFactors, p ∣ d := by
        have hgcd : Nat.gcd u d ≠ 1 := by
          intro h
          exact hcop (Nat.coprime_iff_gcd_eq_one.mpr h)
        obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hgcd
        have hpu : p ∣ u := dvd_trans hpgcd (Nat.gcd_dvd_left u d)
        have hpd : p ∣ d := dvd_trans hpgcd (Nat.gcd_dvd_right u d)
        exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpu, hu.ne'⟩, hpd⟩
      obtain ⟨p, hpf, hpd⟩ := hcommon
      have hcardpos : 0 < (u.primeFactors.filter (fun q => q ∣ d)).card :=
        Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpf, hpd⟩⟩
      have hcardNat : 1 ≤ (u.primeFactors.filter (fun q => q ∣ d)).card :=
        Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcardpos)
      have hcard : (1 : ℝ) ≤
          ((u.primeFactors.filter (fun q => q ∣ d)).card : ℝ) := by
        exact_mod_cast hcardNat
      have hdpos : 0 < d := by
        have hdmem := (Finset.mem_filter.mp hd).1
        exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1
      have hweight : 0 ≤ (d.totient : ℝ)⁻¹ := by positivity
      have hsumCard :
          (∑ p ∈ u.primeFactors, if p ∣ d then (d.totient : ℝ)⁻¹ else 0) =
            ((u.primeFactors.filter (fun q => q ∣ d)).card : ℝ) *
              (d.totient : ℝ)⁻¹ := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      rw [if_neg hcop]
      calc
        (d.totient : ℝ)⁻¹ = 1 * (d.totient : ℝ)⁻¹ := by ring
        _ ≤ ((u.primeFactors.filter (fun q => q ∣ d)).card : ℝ) *
              (d.totient : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcard hweight
        _ = ∑ p ∈ u.primeFactors, if p ∣ d then (d.totient : ℝ)⁻¹ else 0 := hsumCard.symm
  calc
    badSquarefreeReciprocalTotientSum y u ≤
        ∑ d ∈ D, ∑ p ∈ u.primeFactors,
          if p ∣ d then (d.totient : ℝ)⁻¹ else 0 := by
          apply Finset.sum_le_sum
          intro d hd
          exact hPoint d hd
    _ = ∑ p ∈ u.primeFactors, ∑ d ∈ D,
          if p ∣ d then (d.totient : ℝ)⁻¹ else 0 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ u.primeFactors,
          ((p : ℝ) - 1)⁻¹ * reciprocalTotientSquarefreeSum y := by
          apply Finset.sum_le_sum
          intro p hp
          have hpPrime := Nat.prime_of_mem_primeFactors hp
          have hinner :
              (∑ d ∈ D, if p ∣ d then (d.totient : ℝ)⁻¹ else 0) =
                ∑ d ∈ squarefreeModuliDivisibleBy y p, (d.totient : ℝ)⁻¹ := by
            change (∑ d ∈ squarefreeModuli y,
                if p ∣ d then (d.totient : ℝ)⁻¹ else 0) =
              ∑ d ∈ (squarefreeModuli y).filter (fun d => p ∣ d),
                (d.totient : ℝ)⁻¹
            rw [← Finset.sum_filter]
          rw [hinner]
          exact reciprocalTotientSquarefreeDivisibleBy_le y p hpPrime
    _ = reciprocalTotientSquarefreeSum y *
          ∑ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹ := by
          rw [← Finset.sum_mul]
          ring

theorem primeFactors_card_le_natLog (u : ℕ) (hu : 0 < u) :
    u.primeFactors.card ≤ Nat.log 2 u := by
  have hprodLower : 2 ^ u.primeFactors.card ≤ ∏ p ∈ u.primeFactors, p := by
    calc
      2 ^ u.primeFactors.card = ∏ p ∈ u.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ u.primeFactors, p := by
        apply Finset.prod_le_prod
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hprodUpper : (∏ p ∈ u.primeFactors, p) ≤ u :=
    Nat.le_of_dvd hu (Nat.prod_primeFactors_dvd u)
  exact Nat.le_log_of_pow_le Nat.one_lt_two (hprodLower.trans hprodUpper)

theorem candidate_primeFactor_reciprocal_sum_small
    (C : CandidateData) (δ : ℝ) (hB : C.Bounds δ) (jstar : ℕ)
    (hjstar : C.j₀ ≤ jstar) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ u : ℕ, C.weighted x jstar u ≠ 0 →
        (∑ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹) ≤
          K * (L x ^ (19 : ℕ))⁻¹ := by
  obtain ⟨KB, CA, cmin, cmax, hKB, hcmin, hcmax, hbound⟩ := hB
  have hK : 0 < 8 / Real.log 2 := by positivity
  refine ⟨8 / Real.log 2, hK, ?_⟩
  filter_upwards [hbound jstar hjstar,
    Real.tendsto_log_atTop.eventually_ge_atTop 2,
    Filter.eventually_ge_atTop (2 : ℝ)] with x hxBound hxL hx2
  rcases hxBound with ⟨_, _, _, hweight0, _, hsupp⟩
  have hLpos : 0 < L x := by change 0 < Real.log x; linarith
  have hL20pos : 0 < L x ^ (20 : ℕ) := by positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxpos : 0 < x := by linarith
  intro u huWeight
  obtain ⟨hxu, hu2x, hrough⟩ := hsupp u huWeight
  have huPos : 0 < u := by
    have : x ≤ (u : ℝ) := hxu
    exact_mod_cast (lt_of_lt_of_le hxpos this)
  have huRealPos : 0 < (u : ℝ) := by exact_mod_cast huPos
  have hcardNat : u.primeFactors.card ≤ Nat.log 2 u :=
    primeFactors_card_le_natLog u huPos
  have hpowNat : 2 ^ Nat.log 2 u ≤ u := Nat.pow_log_le_self 2 huPos.ne'
  have hpowReal : (2 : ℝ) ^ Nat.log 2 u ≤ (u : ℝ) := by exact_mod_cast hpowNat
  have hlogPow : Real.log ((2 : ℝ) ^ Nat.log 2 u) ≤ Real.log (u : ℝ) :=
    Real.log_le_log (by positivity) hpowReal
  have hlogPowEq : Real.log ((2 : ℝ) ^ Nat.log 2 u) =
      (Nat.log 2 u : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hcardReal : (u.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (u : ℝ) := by
    calc
      (u.primeFactors.card : ℝ) * Real.log 2 ≤
          (Nat.log 2 u : ℝ) * Real.log 2 := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardNat) hlog2pos.le
      _ = Real.log ((2 : ℝ) ^ Nat.log 2 u) := hlogPowEq.symm
      _ ≤ Real.log (u : ℝ) := hlogPow
  have huLog : Real.log (u : ℝ) ≤ 2 * L x := by
    have huUpper := Real.log_le_log huRealPos hu2x
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne'] at huUpper
    have hlogtwo_le : Real.log 2 ≤ L x := by
      have hlogtwo_le_one : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      change Real.log 2 ≤ Real.log x
      exact hlogtwo_le_one.trans (by linarith [hxL])
    change Real.log (u : ℝ) ≤ 2 * Real.log x
    change Real.log (u : ℝ) ≤ Real.log 2 + Real.log x at huUpper
    change Real.log 2 ≤ Real.log x at hlogtwo_le
    linarith
  have hcardBound : (u.primeFactors.card : ℝ) ≤ 2 * L x / Real.log 2 :=
    (le_div_iff₀ hlog2pos).2 (hcardReal.trans huLog)
  have hterm (p : ℕ) (hp : p ∈ u.primeFactors) :
      ((p : ℝ) - 1)⁻¹ ≤ 2 / L x ^ (20 : ℕ) := by
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpLower := (hrough p hpPrime (Nat.dvd_of_mem_primeFactors hp)).1
    have hpCast : L x ^ (20 : ℕ) ≤ (p : ℝ) := by exact_mod_cast hpLower
    have hpow2 : 2 ≤ L x ^ (20 : ℕ) := by
      calc
        (2 : ℝ) ≤ L x := hxL
        _ ≤ L x ^ (20 : ℕ) := by
          have hpow19 : 1 ≤ L x ^ (19 : ℕ) :=
            one_le_pow₀ (show 1 ≤ L x by change 1 ≤ Real.log x; linarith)
          have hmul : L x ≤ L x * L x ^ (19 : ℕ) := by
            simpa using mul_le_mul_of_nonneg_left hpow19 (by linarith : 0 ≤ L x)
          rw [show L x * L x ^ (19 : ℕ) = L x ^ (20 : ℕ) by
            rw [pow_succ]
            ring] at hmul
          exact hmul
    have hpTwo : 2 ≤ (p : ℝ) := hpow2.trans hpCast
    have hpden : L x ^ (20 : ℕ) / 2 ≤ (p : ℝ) - 1 := by
      linarith
    have hdenpos : 0 < (p : ℝ) - 1 := by
      linarith
    have hLdenpos : 0 < L x ^ (20 : ℕ) / 2 := by positivity
    have hinv : ((p : ℝ) - 1)⁻¹ ≤ (L x ^ (20 : ℕ) / 2)⁻¹ :=
      (inv_le_inv₀ hdenpos hLdenpos).2 hpden
    simpa using hinv
  have hsumBound :
      (∑ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹) ≤
        (u.primeFactors.card : ℝ) * (2 / L x ^ (20 : ℕ)) := by
    calc
      _ ≤ ∑ p ∈ u.primeFactors, 2 / L x ^ (20 : ℕ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hterm p hp
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hraw :
      (∑ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹) ≤
        (2 * L x / Real.log 2) * (2 / L x ^ (20 : ℕ)) :=
    hsumBound.trans (mul_le_mul_of_nonneg_right hcardBound (by positivity))
  have hresult :
      (2 * L x / Real.log 2) * (2 / L x ^ (20 : ℕ)) ≤
        (8 / Real.log 2) * (L x ^ (19 : ℕ))⁻¹ := by
    have hpow : L x ^ (20 : ℕ) = L x ^ (19 : ℕ) * L x := by
      rw [pow_succ]
    rw [hpow]
    have hpowPos : 0 < L x ^ (19 : ℕ) := pow_pos hLpos _
    have hEq : (2 * L x / Real.log 2) * (2 / (L x ^ (19 : ℕ) * L x)) =
        (4 / Real.log 2) * (L x ^ (19 : ℕ))⁻¹ := by
      field_simp [ne_of_gt hLpos, ne_of_gt hlog2pos, ne_of_gt hpowPos]
      <;> ring
    rw [hEq]
    have hconst : 4 / Real.log 2 ≤ 8 / Real.log 2 := by
      exact div_le_div_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 8) hlog2pos.le
    exact mul_le_mul_of_nonneg_right hconst (inv_nonneg.mpr hpowPos.le)
  exact hraw.trans hresult

theorem sum_nonCoprimeMass_div_eq_badSquarefreeSum
    (C : CandidateData) (x y : ℝ) (jstar : ℕ) :
    (∑ d ∈ squarefreeModuli y,
      nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) =
      ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
        C.weighted x jstar u * badSquarefreeReciprocalTotientSum y u := by
  classical
  unfold nonCoprimeMass badSquarefreeReciprocalTotientSum
  calc
    _ = ∑ d ∈ squarefreeModuli y, ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
        if Nat.Coprime u d then 0 else
          C.weighted x jstar u * (Nat.totient d : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_filter, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hcop : Nat.Coprime u d <;> simp [hcop, div_eq_mul_inv]
    _ = ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, ∑ d ∈ squarefreeModuli y,
        if Nat.Coprime u d then 0 else
          C.weighted x jstar u * (Nat.totient d : ℝ)⁻¹ := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
        C.weighted x jstar u *
          (∑ d ∈ squarefreeModuli y,
            if Nat.Coprime u d then 0 else (Nat.totient d : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcop : Nat.Coprime u d <;> simp [hcop]
    _ = _ := rfl

theorem candidate_nonCoprimeMass_squarefree_sum_small
    (hc : ClassicalInputs) (C : CandidateData) (δ : ℝ) (hB : C.Bounds δ)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar) (θ : ℝ)
    (hθ : 0 < θ) (hθ' : θ ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ squarefreeModuli (x ^ θ),
        nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) ≤
          K * C.mass x jstar * (L x ^ (18 : ℕ))⁻¹ := by
  obtain ⟨Kprime, hKprime, hprime⟩ :=
    candidate_primeFactor_reciprocal_sum_small C δ hB jstar hjstar
  obtain ⟨Krec, hKrec, hrec0⟩ := reciprocalTotientSquarefreeSum_eventually_le_log hc
  let hpowTop : Tendsto (fun x : ℝ => x ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_id
  have hrec := hpowTop.eventually hrec0
  obtain ⟨KB, CA, cmin, cmax, hKB, hcmin, hcmax, hbound⟩ := hB
  refine ⟨Krec * Kprime, mul_pos hKrec hKprime, ?_⟩
  filter_upwards [hprime, hrec, hbound jstar hjstar,
    Real.tendsto_log_atTop.eventually_ge_atTop 2,
    eventually_ge_atTop (2 : ℝ)] with x hxprime hxrec hxB hxL hx2
  rcases hxB with ⟨_, _, _, hweight0, _, hsupp⟩
  have hLpos : 0 < L x := by change 0 < Real.log x; linarith
  have hxpos : 0 < x := by linarith
  have hlogy : 0 ≤ Real.log (x ^ θ) ∧ Real.log (x ^ θ) ≤ L x := by
    rw [Real.log_rpow hxpos]
    constructor
    · exact mul_nonneg hθ.le hLpos.le
    · exact (mul_le_mul_of_nonneg_right hθ' hLpos.le).trans_eq (by ring)
  have hL18pos : 0 < L x ^ (18 : ℕ) := pow_pos hLpos _
  have hL19pos : 0 < L x ^ (19 : ℕ) := pow_pos hLpos _
  have hpow : L x ^ (19 : ℕ) = L x ^ (18 : ℕ) * L x := by
    rw [pow_succ]
  have hscale :
      Krec * Real.log (x ^ θ) * (Kprime * (L x ^ (19 : ℕ))⁻¹) ≤
        (Krec * Kprime) * (L x ^ (18 : ℕ))⁻¹ := by
    calc
      Krec * Real.log (x ^ θ) * (Kprime * (L x ^ (19 : ℕ))⁻¹) =
          (Krec * Kprime) * (Real.log (x ^ θ) * (L x ^ (19 : ℕ))⁻¹) := by ring
      _ ≤ (Krec * Kprime) * (L x * (L x ^ (19 : ℕ))⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hlogy.2 (inv_nonneg.mpr hL19pos.le))
          (mul_nonneg hKrec.le hKprime.le)
      _ = (Krec * Kprime) * (L x ^ (18 : ℕ))⁻¹ := by
        have hcancel : L x * (L x ^ (19 : ℕ))⁻¹ = (L x ^ (18 : ℕ))⁻¹ := by
          rw [hpow]
          field_simp [ne_of_gt hLpos, ne_of_gt hL18pos]
        rw [hcancel]
  have hbadMassIdentity := sum_nonCoprimeMass_div_eq_badSquarefreeSum C x (x ^ θ) jstar
  have hcoeff (u : ℕ) (hnz : C.weighted x jstar u ≠ 0) :
      badSquarefreeReciprocalTotientSum (x ^ θ) u ≤
        (Krec * Kprime) * (L x ^ (18 : ℕ))⁻¹ := by
    have huPos : 0 < u := by
      have hxu := (hsupp u hnz).1
      exact_mod_cast (lt_of_lt_of_le hxpos hxu)
    have hbad := badSquarefreeReciprocalTotientSum_le_primeFactors
      (x ^ θ) u huPos
    have hpBound := hxprime u hnz
    have hpNonneg : 0 ≤ ∑ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹ := by
      apply Finset.sum_nonneg
      intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpTwo : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.one_le
      exact inv_nonneg.mpr (by linarith)
    calc
      badSquarefreeReciprocalTotientSum (x ^ θ) u ≤
          reciprocalTotientSquarefreeSum (x ^ θ) *
            (∑ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹) := hbad
      _ ≤ (Krec * Real.log (x ^ θ)) *
            (Kprime * (L x ^ (19 : ℕ))⁻¹) := by
          calc
            _ ≤ (Krec * Real.log (x ^ θ)) *
                (∑ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹) :=
                  mul_le_mul_of_nonneg_right hxrec hpNonneg
            _ ≤ _ := mul_le_mul_of_nonneg_left hpBound
                  (mul_nonneg hKrec.le hlogy.1)
      _ ≤ (Krec * Kprime) * (L x ^ (18 : ℕ))⁻¹ := hscale
  have hsumBound :
      (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
        C.weighted x jstar u * badSquarefreeReciprocalTotientSum (x ^ θ) u) ≤
        (Krec * Kprime) * (L x ^ (18 : ℕ))⁻¹ * C.mass x jstar := by
    calc
      _ ≤ ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          C.weighted x jstar u * ((Krec * Kprime) * (L x ^ (18 : ℕ))⁻¹) := by
            apply Finset.sum_le_sum
            intro u hu
            by_cases hzero : C.weighted x jstar u = 0
            · simp [hzero]
            · exact mul_le_mul_of_nonneg_left (hcoeff u hzero) (hweight0 u)
      _ = _ := by
        rw [← Finset.sum_mul]
        simp [CandidateData.mass, mul_comm, mul_assoc]
  calc
    _ = ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
        C.weighted x jstar u * badSquarefreeReciprocalTotientSum (x ^ θ) u :=
          hbadMassIdentity
    _ ≤ (Krec * Kprime) * (L x ^ (18 : ℕ))⁻¹ * C.mass x jstar := hsumBound
    _ = (Krec * Kprime) * C.mass x jstar * (L x ^ (18 : ℕ))⁻¹ := by ring

theorem candidate_nonCoprimeMass_oddSquarefree_sum_small
    (hc : ClassicalInputs) (C : CandidateData) (δ : ℝ) (hB : C.Bounds δ)
    (jstar : ℕ) (hjstar : C.j₀ ≤ jstar) (θ : ℝ)
    (hθ : 0 < θ) (hθ' : θ ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
        nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) ≤
          K * C.mass x jstar * (L x ^ (18 : ℕ))⁻¹ := by
  obtain ⟨K, hK, hprincipal⟩ :=
    candidate_nonCoprimeMass_squarefree_sum_small hc C δ hB jstar hjstar θ hθ hθ'
  obtain ⟨KB, CA, cmin, cmax, hKB, hcmin, hcmax, hbound⟩ := hB
  refine ⟨K, hK, ?_⟩
  filter_upwards [hprincipal, hbound jstar hjstar] with x hprincipal hxB
  rcases hxB with ⟨_, _, _, hweight0, _, _⟩
  let S := (Finset.Icc 1 ⌊x ^ θ⌋₊).filter
    (fun d => Odd d ∧ Squarefree d)
  have hsub : S ⊆ squarefreeModuli (x ^ θ) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdmem, _, hsq⟩
    exact Finset.mem_filter.mpr ⟨hdmem, hsq⟩
  have hnonneg (d : ℕ) :
      0 ≤ nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) := by
    apply div_nonneg
    · unfold nonCoprimeMass
      apply Finset.sum_nonneg
      intro u hu
      exact hweight0 u
    · exact Nat.cast_nonneg _
  calc
    (∑ d ∈ S, nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) ≤
        ∑ d ∈ squarefreeModuli (x ^ θ),
          nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro d hd hnot
      exact hnonneg d
    _ ≤ K * C.mass x jstar * (L x ^ (18 : ℕ))⁻¹ := hprincipal

theorem candidate_remainder_abs_le_nonprincipal_add_correction
    (C : CandidateData) (x : ℝ) (jstar d : ℕ)
    (hd : 0 < d) (hweight0 : ∀ u, 0 ≤ C.weighted x jstar u) :
    |C.remainder x jstar d| ≤
      |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
          C.weighted x jstar u) -
        coprimeMass C x jstar d / (Nat.totient d : ℝ)| +
      nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) := by
  have hsplit := candidate_remainder_principal_split C x jstar d
  have hphi : 0 < (Nat.totient d : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hd
  have hnonneg : 0 ≤ nonCoprimeMass C x jstar d := by
    unfold nonCoprimeMass
    apply Finset.sum_nonneg
    intro u hu
    exact hweight0 u
  have hcorrection : 0 ≤ nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) :=
    div_nonneg hnonneg hphi.le
  have hrewrite : C.remainder x jstar d =
      (∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
        C.weighted x jstar u) -
        coprimeMass C x jstar d / (Nat.totient d : ℝ) -
        nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) := by
    linarith
  calc
    |C.remainder x jstar d| =
        |((∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
            C.weighted x jstar u) -
          coprimeMass C x jstar d / (Nat.totient d : ℝ)) -
          nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)| := by rw [hrewrite]
    _ ≤ |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
          C.weighted x jstar u) -
        coprimeMass C x jstar d / (Nat.totient d : ℝ)| +
        |nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)| := abs_sub _ _
    _ = _ := by rw [abs_of_nonneg hcorrection]

theorem candidate_remainder_sum_bound_of_nonprincipal
    (hc : ClassicalInputs) (C : CandidateData) (δ : ℝ)
    (hB : C.Bounds δ) (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (θ D : ℝ) (hθ : θ < 1 / 2) (_hD : 0 < D)
    (hNonprincipal : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
        |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
            C.weighted x jstar u) -
          coprimeMass C x jstar d / (Nat.totient d : ℝ)|) ≤
        K * (x * L x ^ (-D))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
        |C.remainder x jstar d|) ≤
        K * (x * L x ^ (-D) + C.mass x jstar * L x ^ (-18 : ℝ)) := by
  have hB' := hB
  obtain ⟨KB, CA, cmin, cmax, hKB, hcmin, hcmax, hBounds⟩ := hB'
  obtain ⟨Knp, hKnp, hnp⟩ := hNonprincipal
  by_cases hθpos : 0 < θ
  · have hθle : θ ≤ 1 := by linarith
    obtain ⟨Kp, hKp, hp⟩ :=
      candidate_nonCoprimeMass_oddSquarefree_sum_small hc C δ hB jstar hjstar θ hθpos hθle
    refine ⟨Knp + Kp, add_pos hKnp hKp, ?_⟩
    filter_upwards [hnp, hp, hBounds jstar hjstar,
      eventually_gt_atTop (2 : ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop 2] with x hnpX hpX hBX hx hlog
    rcases hBX with ⟨_, _, _, hweight0, _, _⟩
    have hxpos : 0 < x := by linarith
    have hLpos : 0 < L x := by
      change 0 < Real.log x
      linarith
    have hmass0 : 0 ≤ C.mass x jstar := by
      unfold CandidateData.mass
      apply Finset.sum_nonneg
      intro u hu
      exact hweight0 u
    have hterm1 : 0 ≤ x * L x ^ (-D) :=
      mul_nonneg hxpos.le (Real.rpow_nonneg hLpos.le _)
    have hterm2 : 0 ≤ C.mass x jstar * L x ^ (-18 : ℝ) :=
      mul_nonneg hmass0 (Real.rpow_nonneg hLpos.le _)
    have hpow : (L x ^ (18 : ℕ) : ℝ)⁻¹ = L x ^ (-18 : ℝ) := by
      rw [Real.rpow_neg hLpos.le]
      exact (congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast (L x) 18)).symm
    have hpX' :
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) ≤
          Kp * C.mass x jstar * L x ^ (-18 : ℝ) := by
      calc
        _ ≤ Kp * C.mass x jstar * (L x ^ (18 : ℕ))⁻¹ := hpX
        _ = Kp * C.mass x jstar * L x ^ (-18 : ℝ) := by rw [hpow]
    have hsum :
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          |C.remainder x jstar d|) ≤
          (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
            |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
                C.weighted x jstar u) -
              coprimeMass C x jstar d / (Nat.totient d : ℝ)|) +
          (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
            nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) := by
      calc
        _ ≤ ∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
            (|(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
                C.weighted x jstar u) -
              coprimeMass C x jstar d / (Nat.totient d : ℝ)| +
              nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdpos : 0 < d := by
            have hdi := (Finset.mem_filter.mp hd).1
            exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdi).1
          exact candidate_remainder_abs_le_nonprincipal_add_correction
            C x jstar d hdpos hweight0
        _ = _ := by rw [Finset.sum_add_distrib]
    have hbound :
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          |C.remainder x jstar d|) ≤
          Knp * (x * L x ^ (-D)) +
            Kp * C.mass x jstar * L x ^ (-18 : ℝ) :=
      hsum.trans (add_le_add hnpX hpX')
    refine hbound.trans ?_
    nlinarith [mul_nonneg hKnp.le hterm2, mul_nonneg hKp.le hterm1]
  · have hθnonpos : θ ≤ 0 := le_of_not_gt hθpos
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [hBounds jstar hjstar, eventually_gt_atTop (2 : ℝ)] with x hBX hx
    rcases hBX with ⟨_, _, _, hweight0, _, _⟩
    have hxpos : 0 < x := by linarith
    have hxone : 1 < x := by linarith
    have hlog : 0 ≤ Real.log x := (Real.log_pos hxone).le
    have hθlog : Real.log x * θ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlog hθnonpos
    have hpow : x ^ θ ≤ 1 := by
      rw [Real.rpow_def_of_pos hxpos]
      exact Real.exp_le_one_iff.mpr hθlog
    let S := (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d)
    have hsumzero : (∑ d ∈ S, |C.remainder x jstar d|) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hdI := (Finset.mem_filter.mp hd).1
      have hdle : d ≤ ⌊x ^ θ⌋₊ := (Finset.mem_Icc.mp hdI).2
      have hdleR : (d : ℝ) ≤ 1 := by
        calc
          (d : ℝ) ≤ (⌊x ^ θ⌋₊ : ℝ) := by exact_mod_cast hdle
          _ ≤ x ^ θ := Nat.floor_le (Real.rpow_nonneg hxpos.le θ)
          _ ≤ 1 := hpow
      have hdge : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
      have hdleNat : d ≤ 1 := by exact_mod_cast hdleR
      have hdEq : d = 1 := by omega
      subst d
      have hrem : C.remainder x jstar 1 = 0 := by
        unfold CandidateData.remainder CandidateData.mass
        have hfilter :
            (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => 1 ∣ 2 * u + 1) =
              Finset.Icc 1 ⌊2 * x⌋₊ := by
          ext u
          simp
        rw [hfilter]
        simp [Nat.totient_one]
      rw [hrem]
      simp
    have hLpos : 0 < L x := by
      change 0 < Real.log x
      exact Real.log_pos hxone
    have hmass0 : 0 ≤ C.mass x jstar := by
      unfold CandidateData.mass
      apply Finset.sum_nonneg
      intro u hu
      exact hweight0 u
    have hterm1 : 0 ≤ x * L x ^ (-D) :=
      mul_nonneg hxpos.le (Real.rpow_nonneg hLpos.le _)
    have hterm2 : 0 ≤ C.mass x jstar * L x ^ (-18 : ℝ) :=
      mul_nonneg hmass0 (Real.rpow_nonneg hLpos.le _)
    rw [hsumzero]
    positivity

theorem candidate_typeI_of_nonprincipal_bounds
    (hc : ClassicalInputs) (C : CandidateData) (δ : ℝ) (hB : C.Bounds δ)
    (hNonprincipal : ∀ θ D : ℝ, θ < 1 / 2 → 0 < D →
      ∀ jstar : ℕ, C.j₀ ≤ jstar → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1),
              C.weighted x jstar u) -
            coprimeMass C x jstar d / (Nat.totient d : ℝ)|) ≤
          K * (x * L x ^ (-D))) :
    C.TypeI := by
  intro θ D hθ hD jstar hjstar
  exact candidate_remainder_sum_bound_of_nonprincipal hc C δ hB jstar hjstar
    θ D hθ hD (hNonprincipal θ D hθ hD jstar hjstar)

theorem candidate_remainder_one (C : CandidateData) (x : ℝ) (jstar : ℕ) :
    C.remainder x jstar 1 = 0 := by
  unfold CandidateData.remainder CandidateData.mass
  have hfilter :
      (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => 1 ∣ 2 * u + 1) =
        Finset.Icc 1 ⌊2 * x⌋₊ := by
    ext u
    simp
  rw [hfilter]
  simp [Nat.totient_one]

end Erdos821.P7B

