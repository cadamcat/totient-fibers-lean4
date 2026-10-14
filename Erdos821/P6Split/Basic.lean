import Erdos821.S56.SlotSplitTasks
import Erdos821.S56.Separated
import Erdos821.S56.BlueprintInvariant
import Erdos821.S56.SlotProduct
import Erdos821.S56.AllocationRange
import Erdos821.S56.CoefficientSplit
import Erdos821.S56.ProcessedSlots
import Erdos821.S56.Allocation
import Erdos821.S56.GroupFreeDivision
import Erdos821.S56.SumCoefficientTask
import Erdos821.P6Sum.SumCoefficientTask

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
attribute [local instance] Erdos821.S56Core.sumCoordinateFintype

namespace Erdos821.P6Split
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

abbrev ProcessedValue (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : Erdos821.S56Core.ProcessedIndex D x jstar) :=
  {p : ℕ // p ∈ D.band x (Erdos821.S56Core.processedSlot D x jstar i).1.val}

def processedCoefficient (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ) (v : ℕ) : ℂ :=
  Erdos821.S56Core.productCoefficient
    (fun i : {i // delta i = take} => ProcessedValue D x jstar i.val)
    (fun _ p => p.val)
    (fun i p => Erdos821.Blueprint.Analytic.mellin p.val (nu i.val)) v

def SlotCoefficientSplitTask : Prop :=
  ∀ (D : BandData) (x : ℝ) (jstar : ℕ),
    jstar ≤ D.last x → 1 ≤ D.r₀ →
    (∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g)) →
    (∀ p : ℕ, rough (W x) p → Erdos821.S56Core.GroupFree (D.groups x) p) →
    ∀ (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
      (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ)
      (u e : ℕ), 0 < u → 0 < e →
      (∑ z : D.Lists x jstar,
        if D.listProduct z =
            groupFreePart (D.groups x) u ∧
            Erdos821.S56Core.processedFactor D z delta = e then
          (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℂ) *
            ∏ i, Erdos821.Blueprint.Analytic.mellin
              (z (Erdos821.S56Core.processedSlot D x jstar i)).val (nu i)
        else 0) =
      if e ∣ u then
        processedCoefficient D x jstar delta true nu e *
          (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) (u / e) : ℂ) *
            Erdos821.S56Core.roughCore x (Real.exp (D.c₁ * D.scale x jstar))
              (Real.exp (D.c₂ * D.scale x jstar)) 0
              (processedCoefficient D x jstar delta false nu)
              (groupFreePart (D.groups x) (u / e))
      else 0

-- sanity: our copy agrees with the lead's statement
example : SlotCoefficientSplitTask = Erdos821.S56Core.SlotCoefficientSplitTask :=
  rfl

/-- `mellin n 0 = 1`. -/
theorem mellin_zero (n : ℝ) : Erdos821.Blueprint.Analytic.mellin n 0 = 1 := by
  unfold Erdos821.Blueprint.Analytic.mellin
  simp

theorem processedSlot_ne_exc (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (i : Erdos821.S56Core.ProcessedIndex D x jstar) :
    Erdos821.S56Core.processedSlot D x jstar i ≠
      Erdos821.S56Core.exceptionalSlot D x jstar hj hr := by
  intro h
  have hne := Erdos821.S56Core.processed_not_exceptional D x jstar i
  have h1 : (Erdos821.S56Core.processedSlot D x jstar i).1.val = jstar :=
    congrArg (fun s : D.Slot x => s.1.val) h |>
      fun hh => hh.trans (by rfl)
  have h2 : (Erdos821.S56Core.processedSlot D x jstar i).2.val = 0 :=
    congrArg (fun s : D.Slot x => s.2.val) h |>
      fun hh => hh.trans (by rfl)
  exact hne ⟨h1, h2⟩

/-- The exceptional slot uses the rough interval, not the prime band. -/
theorem slotValues_exc (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) :
    D.slotValues x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) =
      (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x jstar)⌉₊
        ⌊Real.exp (D.c₂ * D.scale x jstar)⌋₊).filter (rough (W x)) := by
  unfold BandData.slotValues
  have hcond : ((Erdos821.S56Core.exceptionalSlot D x jstar hj hr).1.val = jstar ∧
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr).2.val = 0) :=
    ⟨by rfl, by rfl⟩
  simp only [hcond, and_self, ite_true]

/-- Membership in the exceptional slotValues in analytic form. -/
theorem mem_slotValues_exc_iff (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) (v : ℕ) :
    v ∈ D.slotValues x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) ↔
      Real.exp (D.c₁ * D.scale x jstar) ≤ (v : ℝ) ∧ (v : ℝ) ≤
        Real.exp (D.c₂ * D.scale x jstar) ∧ rough (W x) v := by
  rw [slotValues_exc D x jstar hj hr]
  constructor
  · intro hv
    obtain ⟨hmem, hrough⟩ := Finset.mem_filter.mp hv
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmem
    refine ⟨Nat.ceil_le.mp hlo, ?_, hrough⟩
    exact (Nat.le_floor_iff (Real.exp_pos _).le).mp hhi
  · rintro ⟨hlo, hhi, hrough⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, ?_⟩, hrough⟩
    exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr hhi

/-- Non-exceptional slots use the prime band. -/
theorem slotValues_eq_band_of_ne (D : BandData) (x : ℝ) (jstar : ℕ)
    (s : D.Slot x) (hne : ¬(s.1.val = jstar ∧ s.2.val = 0)) :
    D.slotValues x jstar s = D.band x s.1.val := by
  unfold BandData.slotValues
  simp only [hne, ite_false]

/-- A single band prime is group-free under disjointness. -/
theorem single_band_GroupFree (D : BandData) (x : ℝ) (s : D.Slot x) (v : ℕ)
    (hv : v ∈ D.band x s.1.val)
    (hdisj : ∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g)) :
    Erdos821.S56Core.GroupFree (D.groups x) v := by
  have hzprime : v.Prime := (Finset.mem_filter.mp hv).2
  have hsle : s.1.val ≤ D.last x := Nat.le_of_lt_succ s.1.isLt
  intro p hp hdiv
  obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
  have hprime_g := (D.groups x).prime g p hpg
  have heq : p = v := (Nat.prime_dvd_prime_iff_eq hprime_g hzprime).mp hdiv
  subst heq
  exact Finset.disjoint_left.mp (hdisj s.1.val hsle g) hv hpg

/-- Every processed slot value is group-free. -/
theorem processed_value_GroupFree (D : BandData) (x : ℝ) (jstar : ℕ)
    (hdisj : ∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g))
    (z : D.Lists x jstar) (i : Erdos821.S56Core.ProcessedIndex D x jstar) :
    Erdos821.S56Core.GroupFree (D.groups x)
      (z (Erdos821.S56Core.processedSlot D x jstar i)).val := by
  have hne : ¬((Erdos821.S56Core.processedSlot D x jstar i).1.val = jstar ∧
      (Erdos821.S56Core.processedSlot D x jstar i).2.val = 0) :=
    Erdos821.S56Core.processed_not_exceptional D x jstar i
  have h_eq : D.slotValues x jstar (Erdos821.S56Core.processedSlot D x jstar i) =
      D.band x (Erdos821.S56Core.processedSlot D x jstar i).1.val :=
    slotValues_eq_band_of_ne D x jstar _ hne
  have hprop : (z (Erdos821.S56Core.processedSlot D x jstar i)).val ∈
      D.slotValues x jstar (Erdos821.S56Core.processedSlot D x jstar i) :=
    (z _).property
  have hmem : (z (Erdos821.S56Core.processedSlot D x jstar i)).val ∈
      D.band x (Erdos821.S56Core.processedSlot D x jstar i).1.val :=
    Eq.subst (motive := fun (t : Finset ℕ) =>
      (z (Erdos821.S56Core.processedSlot D x jstar i)).val ∈ t) h_eq hprop
  exact single_band_GroupFree D x _ _ hmem hdisj

/-- The take factor is group-free. -/
theorem processedFactor_GroupFree (D : BandData) (x : ℝ) (jstar : ℕ)
    (hdisj : ∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g))
    (z : D.Lists x jstar)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) :
    Erdos821.S56Core.GroupFree (D.groups x)
      (Erdos821.S56Core.processedFactor D z delta) := by
  unfold Erdos821.S56Core.processedFactor
  apply Erdos821.S56Core.groupFree_prod
  intro i _
  by_cases hd : delta i = true
  · rw [hd]
    simp only [↓reduceIte]
    exact processed_value_GroupFree D x jstar hdisj z i
  · have hd' : delta i = false := Bool.eq_false_iff.mpr hd
    rw [hd']
    simp only [Bool.false_eq_true, ↓reduceIte]
    intro p hp hdiv
    obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
    exact ((D.groups x).prime g p hpg).not_dvd_one hdiv

/-- Any take-assignment product is group-free. -/
theorem takeProduct_GroupFree (D : BandData) (x : ℝ) (jstar : ℕ)
    (hdisj : ∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g))
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) (take : Bool)
    (w : (i : {i // delta i = take}) → ProcessedValue D x jstar i.val) :
    Erdos821.S56Core.GroupFree (D.groups x) (∏ i, (w i).val) := by
  apply Erdos821.S56Core.groupFree_prod
  intro i _
  exact single_band_GroupFree D x
    (Erdos821.S56Core.processedSlot D x jstar i.val) _ (w i).property hdisj

/-- Take coefficient vanishes on non-group-free targets. -/
theorem takeCoeff_eq_zero_of_not_GroupFree (D : BandData) (x : ℝ) (jstar : ℕ)
    (hdisj : ∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g))
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ)
    (e : ℕ) (hfree : ¬Erdos821.S56Core.GroupFree (D.groups x) e) :
    processedCoefficient D x jstar delta true nu e = 0 := by
  unfold processedCoefficient Erdos821.S56Core.productCoefficient
  apply Finset.sum_eq_zero
  intro w _
  have hprod_free := takeProduct_GroupFree D x jstar hdisj delta true w
  have hne : ∏ i, (fun (i : {i // delta i = true}) => (w i).val) i ≠ e := by
    intro heq
    exact hfree (heq ▸ hprod_free)
  simp only [hne, ite_false]

/-- The take factor divides the full list product. -/
theorem processedFactor_dvd_listProduct (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (z : D.Lists x jstar)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) :
    Erdos821.S56Core.processedFactor D z delta ∣ D.listProduct z := by
  have hprod := Erdos821.S56Core.processed_factor_product D z delta
  have hexc := Erdos821.S56Core.pure_product_exceptional D z hj hr
  use (Erdos821.S56Core.processedFactor D z (fun i => !(delta i)) *
    (z (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)).val)
  calc D.listProduct z
      = Erdos821.S56Core.pureProduct D z *
        (z (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)).val :=
        hexc.symm
    _ = (Erdos821.S56Core.processedFactor D z delta *
        Erdos821.S56Core.processedFactor D z (fun i => !(delta i))) *
        (z (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)).val := by
        rw [← hprod]
    _ = Erdos821.S56Core.processedFactor D z delta *
        (Erdos821.S56Core.processedFactor D z (fun i => !(delta i)) *
          (z (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)).val) := by
        ring

/-- Every non-exceptional slot is a processed slot. -/
theorem processedSlot_surjective_complement (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) (s : D.Slot x)
    (hne : s ≠ Erdos821.S56Core.exceptionalSlot D x jstar hj hr) :
    ∃ i : Erdos821.S56Core.ProcessedIndex D x jstar,
      Erdos821.S56Core.processedSlot D x jstar i = s := by
  let q : Erdos821.S56Core.AllSlotIndex D x :=
    (Erdos821.S56Core.decodeSlot D x).symm s
  let qexc : Erdos821.S56Core.AllSlotIndex D x :=
    (Erdos821.S56Core.decodeSlot D x).symm
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)
  have hq_ne : q ≠ qexc := by
    intro heq
    apply hne
    have hs : Erdos821.S56Core.decodeSlot D x q = s :=
      (Erdos821.S56Core.decodeSlot D x).apply_symm_apply s
    have hexc : Erdos821.S56Core.decodeSlot D x qexc =
        Erdos821.S56Core.exceptionalSlot D x jstar hj hr :=
      (Erdos821.S56Core.decodeSlot D x).apply_symm_apply _
    rw [← hs, ← hexc, heq]
  have hq_mem : q ∈ Erdos821.S56Core.pureIndices D x jstar := by
    rw [Erdos821.S56Core.pure_indices_erase D x jstar hj hr]
    exact Finset.mem_erase.mpr ⟨hq_ne, Finset.mem_univ q⟩
  let iso := (Erdos821.S56Core.pureIndices D x jstar).orderIsoOfFin rfl
  let i : Erdos821.S56Core.ProcessedIndex D x jstar := iso.symm ⟨q, hq_mem⟩
  use i
  have hi : iso i = ⟨q, hq_mem⟩ := OrderIso.apply_symm_apply iso ⟨q, hq_mem⟩
  have hval : ((Erdos821.S56Core.pureIndices D x jstar).orderIsoOfFin rfl i).val = q := by
    have hsub := congrArg Subtype.val hi
    simpa [iso] using hsub
  have hdecode : Erdos821.S56Core.decodeSlot D x
      (((Erdos821.S56Core.pureIndices D x jstar).orderIsoOfFin rfl i).val) = s := by
    rw [hval]
    show Erdos821.S56Core.decodeSlot D x q = s
    exact (Erdos821.S56Core.decodeSlot D x).apply_symm_apply s
  simpa [Erdos821.S56Core.processedSlot] using hdecode

/-- From a slot different from exceptional, recover the processed index. -/
def indexOf (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) (s : D.Slot x)
    (hne : s ≠ Erdos821.S56Core.exceptionalSlot D x jstar hj hr) :
    Erdos821.S56Core.ProcessedIndex D x jstar :=
  Classical.choose (processedSlot_surjective_complement D x jstar hj hr s hne)

theorem indexOf_spec (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) (s : D.Slot x)
    (hne : s ≠ Erdos821.S56Core.exceptionalSlot D x jstar hj hr) :
    Erdos821.S56Core.processedSlot D x jstar (indexOf D x jstar hj hr s hne) = s :=
  Classical.choose_spec (processedSlot_surjective_complement D x jstar hj hr s hne)

/-- Band membership of a processed slot value. -/
theorem processed_band_mem (D : BandData) (x : ℝ) (jstar : ℕ)
    (z : D.Lists x jstar) (i : Erdos821.S56Core.ProcessedIndex D x jstar) :
    (z (Erdos821.S56Core.processedSlot D x jstar i)).val ∈
      D.band x (Erdos821.S56Core.processedSlot D x jstar i).1.val := by
  have hne : ¬((Erdos821.S56Core.processedSlot D x jstar i).1.val = jstar ∧
      (Erdos821.S56Core.processedSlot D x jstar i).2.val = 0) :=
    Erdos821.S56Core.processed_not_exceptional D x jstar i
  have h_eq : D.slotValues x jstar (Erdos821.S56Core.processedSlot D x jstar i) =
      D.band x (Erdos821.S56Core.processedSlot D x jstar i).1.val :=
    slotValues_eq_band_of_ne D x jstar _ hne
  have hprop : (z (Erdos821.S56Core.processedSlot D x jstar i)).val ∈
      D.slotValues x jstar (Erdos821.S56Core.processedSlot D x jstar i) :=
    (z _).property
  exact Eq.subst (motive := fun (t : Finset ℕ) =>
    (z (Erdos821.S56Core.processedSlot D x jstar i)).val ∈ t) h_eq hprop

/-- Project a full list to its triple components. -/
def toTriple (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (z : D.Lists x jstar) :
    (D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)) ×
    ((i : {i // delta i = true}) → ProcessedValue D x jstar i.val) ×
    ((i : {i // delta i = false}) → ProcessedValue D x jstar i.val) :=
  (z (Erdos821.S56Core.exceptionalSlot D x jstar hj hr),
    (fun i => ⟨(z (Erdos821.S56Core.processedSlot D x jstar i.val)).val,
      processed_band_mem D x jstar z i.val⟩),
    (fun i => ⟨(z (Erdos821.S56Core.processedSlot D x jstar i.val)).val,
      processed_band_mem D x jstar z i.val⟩))

/-- Reassemble a list from triple components (constructive via `indexOf`). -/
def ofTriple (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (t : (D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)) ×
      ((i : {i // delta i = true}) → ProcessedValue D x jstar i.val) ×
      ((i : {i // delta i = false}) → ProcessedValue D x jstar i.val))
    (s : D.Slot x) : D.SlotValue x jstar s := by
  by_cases hs : s = Erdos821.S56Core.exceptionalSlot D x jstar hj hr
  · subst hs
    exact t.1
  · have hne_vals : ¬(s.1.val = jstar ∧ s.2.val = 0) := by
      intro hcon
      apply hs
      have hj1 : s.1.val = jstar := hcon.1
      have hj2 : s.2.val = 0 := hcon.2
      have h1 : s.1 =
          (Erdos821.S56Core.exceptionalSlot D x jstar hj hr).1 := by
        apply Fin.ext
        show s.1.val = _
        rw [hj1]
        rfl
      have h2 : s.2 =
          (Erdos821.S56Core.exceptionalSlot D x jstar hj hr).2 := by
        apply Fin.ext
        show s.2.val = _
        rw [hj2]
        rfl
      exact Prod.ext h1 h2
    have h_eq : D.slotValues x jstar s = D.band x s.1.val :=
      slotValues_eq_band_of_ne D x jstar s hne_vals
    let ii := indexOf D x jstar hj hr s hs
    have hii : Erdos821.S56Core.processedSlot D x jstar ii = s :=
      indexOf_spec D x jstar hj hr s hs
    by_cases hdelta : delta ii = true
    · have hmem : (t.2.1 ⟨ii, hdelta⟩).val ∈ D.slotValues x jstar s := by
        have hband : (t.2.1 ⟨ii, hdelta⟩).val ∈ D.band x s.1.val := by
          have hprop : (t.2.1 ⟨ii, hdelta⟩).val ∈
              D.band x (Erdos821.S56Core.processedSlot D x jstar ii).1.val :=
            (t.2.1 ⟨ii, hdelta⟩).property
          have hband_eq : D.band x
              (Erdos821.S56Core.processedSlot D x jstar ii).1.val =
              D.band x s.1.val := by rw [hii]
          exact Eq.subst (motive := fun (tt : Finset ℕ) =>
            (t.2.1 ⟨ii, hdelta⟩).val ∈ tt) hband_eq hprop
        exact Eq.subst (motive := fun (tt : Finset ℕ) =>
          (t.2.1 ⟨ii, hdelta⟩).val ∈ tt) h_eq.symm hband
      exact ⟨(t.2.1 ⟨ii, hdelta⟩).val, hmem⟩
    · have hfalse : delta ii = false := Bool.eq_false_iff.mpr (fun h => hdelta h)
      have hmem : (t.2.2 ⟨ii, hfalse⟩).val ∈ D.slotValues x jstar s := by
        have hband : (t.2.2 ⟨ii, hfalse⟩).val ∈ D.band x s.1.val := by
          have hprop : (t.2.2 ⟨ii, hfalse⟩).val ∈
              D.band x (Erdos821.S56Core.processedSlot D x jstar ii).1.val :=
            (t.2.2 ⟨ii, hfalse⟩).property
          have hband_eq : D.band x
              (Erdos821.S56Core.processedSlot D x jstar ii).1.val =
              D.band x s.1.val := by rw [hii]
          exact Eq.subst (motive := fun (tt : Finset ℕ) =>
            (t.2.2 ⟨ii, hfalse⟩).val ∈ tt) hband_eq hprop
        exact Eq.subst (motive := fun (tt : Finset ℕ) =>
          (t.2.2 ⟨ii, hfalse⟩).val ∈ tt) h_eq.symm hband
      exact ⟨(t.2.2 ⟨ii, hfalse⟩).val, hmem⟩

/-- `indexOf` recovers the original index on processed slots. -/
theorem indexOf_processedSlot (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (i : Erdos821.S56Core.ProcessedIndex D x jstar) :
    indexOf D x jstar hj hr (Erdos821.S56Core.processedSlot D x jstar i)
      (processedSlot_ne_exc D x jstar hj hr i) = i := by
  apply Erdos821.S56Core.processedSlot_injective D x jstar
  exact indexOf_spec D x jstar hj hr _ _

/-- Reassembling the projection recovers the list. -/
theorem ofTriple_toTriple (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (z : D.Lists x jstar) :
    (fun s => ofTriple D x jstar hj hr delta (toTriple D x jstar hj hr delta z) s) = z := by
  funext s
  apply Subtype.ext
  show ((ofTriple D x jstar hj hr delta (toTriple D x jstar hj hr delta z) s).val) = _
  unfold ofTriple toTriple
  by_cases hs : s = Erdos821.S56Core.exceptionalSlot D x jstar hj hr
  · subst hs
    simp only [dite_true]
  · simp only [hs, dite_false]
    have hii : Erdos821.S56Core.processedSlot D x jstar
        (indexOf D x jstar hj hr s hs) = s :=
      indexOf_spec D x jstar hj hr s hs
    by_cases hdelta : delta (indexOf D x jstar hj hr s hs) = true
    · simp only [hdelta, dite_true]
      have heq : (z (Erdos821.S56Core.processedSlot D x jstar
          (indexOf D x jstar hj hr s hs))).val = (z s).val := by rw [hii]
      exact heq
    · have hfalse : delta (indexOf D x jstar hj hr s hs) = false :=
        Bool.eq_false_iff.mpr (fun h => hdelta h)
      simp only [hfalse]
      -- the inner dite in ofTriple is on `delta ii = true`, now false;
      -- need to show skip branch equals
      have heq : (z (Erdos821.S56Core.processedSlot D x jstar
          (indexOf D x jstar hj hr s hs))).val = (z s).val := by rw [hii]
      -- After simp, goal should be this equality up to unfolding take/skip funs
      simpa using heq

/-- Projecting the reassembly recovers the triple. -/
theorem toTriple_ofTriple (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (t : (D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)) ×
      ((i : {i // delta i = true}) → ProcessedValue D x jstar i.val) ×
      ((i : {i // delta i = false}) → ProcessedValue D x jstar i.val)) :
    toTriple D x jstar hj hr delta (fun s => ofTriple D x jstar hj hr delta t s) = t := by
  obtain ⟨ve, wt, ws⟩ := t
  simp only [toTriple]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- exceptional part
    apply Subtype.ext
    show ((ofTriple D x jstar hj hr delta (ve, wt, ws)
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)).val) = _
    unfold ofTriple
    simp only [dite_true]
  · -- take part
    funext i
    apply Subtype.ext
    show (((ofTriple D x jstar hj hr delta (ve, wt, ws)
      (Erdos821.S56Core.processedSlot D x jstar i.val)).val)) = _
    have hne : Erdos821.S56Core.processedSlot D x jstar i.val ≠
        Erdos821.S56Core.exceptionalSlot D x jstar hj hr := by
      apply processedSlot_ne_exc
    have hii : indexOf D x jstar hj hr
        (Erdos821.S56Core.processedSlot D x jstar i.val) hne = i.val := by
      apply indexOf_processedSlot
    have hdelta_true : delta (indexOf D x jstar hj hr
        (Erdos821.S56Core.processedSlot D x jstar i.val) hne) = true := by
      rw [hii]; exact i.property
    have hsub : ((⟨indexOf D x jstar hj hr
        (Erdos821.S56Core.processedSlot D x jstar i.val) hne,
        hdelta_true⟩ : {i // delta i = true})) = i := Subtype.ext hii
    have heq : ((wt ⟨indexOf D x jstar hj hr
        (Erdos821.S56Core.processedSlot D x jstar i.val) hne,
        hdelta_true⟩).val : ℕ) = (wt i).val := by rw [hsub]
    unfold ofTriple
    simp only [hne, dite_false, hdelta_true, dite_true]
    exact heq
  · -- skip part
    funext i
    apply Subtype.ext
    show (((ofTriple D x jstar hj hr delta (ve, wt, ws)
      (Erdos821.S56Core.processedSlot D x jstar i.val)).val)) = _
    have hne : Erdos821.S56Core.processedSlot D x jstar i.val ≠
        Erdos821.S56Core.exceptionalSlot D x jstar hj hr := by
      apply processedSlot_ne_exc
    have hii : indexOf D x jstar hj hr
        (Erdos821.S56Core.processedSlot D x jstar i.val) hne = i.val := by
      apply indexOf_processedSlot
    have hfalse : delta (indexOf D x jstar hj hr
        (Erdos821.S56Core.processedSlot D x jstar i.val) hne) = false := by
      rw [hii]; exact i.property
    have hsub : ((⟨indexOf D x jstar hj hr
        (Erdos821.S56Core.processedSlot D x jstar i.val) hne,
        hfalse⟩ : {i // delta i = false})) = i := Subtype.ext hii
    have heq : ((ws ⟨indexOf D x jstar hj hr
        (Erdos821.S56Core.processedSlot D x jstar i.val) hne,
        hfalse⟩).val : ℕ) = (ws i).val := by rw [hsub]
    unfold ofTriple
    simp only [hne, dite_false, hfalse]
    exact heq

/-- The triple decomposition as an explicit equivalence. -/
def tripleEquiv (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) :
    D.Lists x jstar ≃
      ((D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)) ×
        ((i : {i // delta i = true}) → ProcessedValue D x jstar i.val) ×
        ((i : {i // delta i = false}) → ProcessedValue D x jstar i.val)) :=
  { toFun := toTriple D x jstar hj hr delta
    invFun := fun t s => ofTriple D x jstar hj hr delta t s
    left_inv := fun z => by
      have h := ofTriple_toTriple D x jstar hj hr delta z
      simpa using h
    right_inv := fun t => toTriple_ofTriple D x jstar hj hr delta t }

/-- `processedFactor` equals the take-subtype product. -/
theorem processedFactor_eq_takeProd (D : BandData) (x : ℝ) (jstar : ℕ)
    (z : D.Lists x jstar)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) :
    Erdos821.S56Core.processedFactor D z delta =
      ∏ i : {i // delta i = true},
        (z (Erdos821.S56Core.processedSlot D x jstar i.val)).val := by
  have hfilter : (∏ i : Erdos821.S56Core.ProcessedIndex D x jstar,
      if delta i = true then
        (z (Erdos821.S56Core.processedSlot D x jstar i)).val else 1) =
      ∏ i : {i // delta i = true},
        (z (Erdos821.S56Core.processedSlot D x jstar i.val)).val := by
    have h1 : (∏ i : Erdos821.S56Core.ProcessedIndex D x jstar,
        if delta i = true then
          (z (Erdos821.S56Core.processedSlot D x jstar i)).val else 1) =
        ∏ i ∈ Finset.univ.filter (fun i => delta i = true),
          (z (Erdos821.S56Core.processedSlot D x jstar i)).val := by
      rw [← Finset.prod_filter]
    have h2 : (∏ i ∈ Finset.univ.filter (fun i => delta i = true),
        (z (Erdos821.S56Core.processedSlot D x jstar i)).val) =
        ∏ i : {i // delta i = true},
          (z (Erdos821.S56Core.processedSlot D x jstar i.val)).val := by
      apply Finset.prod_subtype
      intro i
      simp
    rw [h1, h2]
  -- `if delta i then ...` is `if delta i = true then ...` after elaboration
  exact hfilter

/-- Values of the reassembled list at the exceptional slot. -/
theorem ofTriple_exc_val (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (ve : D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
    (wt : (i : {i // delta i = true}) → ProcessedValue D x jstar i.val)
    (ws : (i : {i // delta i = false}) → ProcessedValue D x jstar i.val) :
    ((ofTriple D x jstar hj hr delta (ve, wt, ws)
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)).val) = ve.val := by
  have h := toTriple_ofTriple D x jstar hj hr delta (ve, wt, ws)
  have h1 : (toTriple D x jstar hj hr delta
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)).1 = ve := by
    rw [h]
  have h2 : ((toTriple D x jstar hj hr delta
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)).1).val = ve.val := by
    rw [h1]
  simpa [toTriple] using h2

/-- Values of the reassembled list at take slots. -/
theorem ofTriple_take_val (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (ve : D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
    (wt : (i : {i // delta i = true}) → ProcessedValue D x jstar i.val)
    (ws : (i : {i // delta i = false}) → ProcessedValue D x jstar i.val)
    (i : {i // delta i = true}) :
    ((ofTriple D x jstar hj hr delta (ve, wt, ws)
      (Erdos821.S56Core.processedSlot D x jstar i.val)).val) = (wt i).val := by
  have h := toTriple_ofTriple D x jstar hj hr delta (ve, wt, ws)
  have htake : (toTriple D x jstar hj hr delta
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)).2.1 = wt := by
    rw [h]
  have hi : (toTriple D x jstar hj hr delta
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)).2.1 i = wt i :=
    congrFun htake i
  have hval : ((((toTriple D x jstar hj hr delta
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)).2.1 i).val)) =
      (wt i).val := congrArg Subtype.val hi
  simpa [toTriple] using hval

/-- Values of the reassembled list at skip slots. -/
theorem ofTriple_skip_val (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (ve : D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
    (wt : (i : {i // delta i = true}) → ProcessedValue D x jstar i.val)
    (ws : (i : {i // delta i = false}) → ProcessedValue D x jstar i.val)
    (i : {i // delta i = false}) :
    ((ofTriple D x jstar hj hr delta (ve, wt, ws)
      (Erdos821.S56Core.processedSlot D x jstar i.val)).val) = (ws i).val := by
  have h := toTriple_ofTriple D x jstar hj hr delta (ve, wt, ws)
  have hskip : (toTriple D x jstar hj hr delta
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)).2.2 = ws := by
    rw [h]
  have hi : (toTriple D x jstar hj hr delta
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)).2.2 i = ws i :=
    congrFun hskip i
  have hval : ((((toTriple D x jstar hj hr delta
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)).2.2 i).val)) =
      (ws i).val := congrArg Subtype.val hi
  simpa [toTriple] using hval

/-- Split a processed product into take × skip (any commutative monoid). -/
theorem pureProduct_split {M : Type*} [CommMonoid M]
    (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (f : Erdos821.S56Core.ProcessedIndex D x jstar → M) :
    (∏ i, f i) =
      (∏ i : {i // delta i = true}, f i.val) *
      (∏ i : {i // delta i = false}, f i.val) := by
  have htake : (∏ i : {i // delta i = true}, f i.val) =
      ∏ i ∈ Finset.univ.filter (fun i => delta i = true), f i := by
    symm
    apply Finset.prod_subtype
    intro i
    simp
  have hskip : (∏ i : {i // delta i = false}, f i.val) =
      ∏ i ∈ Finset.univ.filter (fun i => ¬(delta i = true)), f i := by
    symm
    apply Finset.prod_subtype
    intro i
    constructor
    · intro hmem
      obtain ⟨_, hnot⟩ := Finset.mem_filter.mp hmem
      exact Bool.eq_false_iff.mpr hnot
    · intro hfalse
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hfalse]
      decide
  rw [htake, hskip]
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Erdos821.S56Core.ProcessedIndex D x jstar => delta i = true) f
  -- hsplit : (∏ filter true) * (∏ filter ¬true) = ∏ univ
  rw [hsplit]

/-- List product of a reassembled triple. -/
theorem listProduct_ofTriple (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (ve : D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
    (wt : (i : {i // delta i = true}) → ProcessedValue D x jstar i.val)
    (ws : (i : {i // delta i = false}) → ProcessedValue D x jstar i.val) :
    D.listProduct (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s) =
      ve.val * (∏ i : {i // delta i = true}, (wt i).val) *
        (∏ i : {i // delta i = false}, (ws i).val) := by
  have hexc := Erdos821.S56Core.pure_product_exceptional
    (D := D) (x := x) (jstar := jstar)
    (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s) hj hr
  have hpure : Erdos821.S56Core.pureProduct D
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s) =
      (∏ i : {i // delta i = true}, (wt i).val) *
        (∏ i : {i // delta i = false}, (ws i).val) := by
    unfold Erdos821.S56Core.pureProduct
    have hsplit := pureProduct_split (M := ℕ) D x jstar delta
      (fun i => ((ofTriple D x jstar hj hr delta (ve, wt, ws)
        (Erdos821.S56Core.processedSlot D x jstar i)).val))
    rw [hsplit]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      exact ofTriple_take_val D x jstar hj hr delta ve wt ws i
    · apply Finset.prod_congr rfl
      intro i _
      exact ofTriple_skip_val D x jstar hj hr delta ve wt ws i
  have hexc_val : ((fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)).val = ve.val := by
    have h := ofTriple_exc_val D x jstar hj hr delta ve wt ws
    simpa using h
  calc D.listProduct (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)
      = Erdos821.S56Core.pureProduct D
          (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s) *
        ((fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)
          (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)).val := hexc.symm
    _ = _ := by rw [hpure, hexc_val]; ring

/-- Take factor of a reassembled triple. -/
theorem processedFactor_ofTriple (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (ve : D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
    (wt : (i : {i // delta i = true}) → ProcessedValue D x jstar i.val)
    (ws : (i : {i // delta i = false}) → ProcessedValue D x jstar i.val) :
    Erdos821.S56Core.processedFactor D
      (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s) delta =
      ∏ i : {i // delta i = true}, (wt i).val := by
  have htake := processedFactor_eq_takeProd D x jstar
    (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s) delta
  rw [htake]
  apply Finset.prod_congr rfl
  intro i _
  exact ofTriple_take_val D x jstar hj hr delta ve wt ws i

/-- Mellin product of a reassembled triple splits. -/
theorem mellinProd_ofTriple (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ)
    (ve : D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
    (wt : (i : {i // delta i = true}) → ProcessedValue D x jstar i.val)
    (ws : (i : {i // delta i = false}) → ProcessedValue D x jstar i.val) :
    (∏ i : Erdos821.S56Core.ProcessedIndex D x jstar,
      Erdos821.Blueprint.Analytic.mellin
        ((fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)
          (Erdos821.S56Core.processedSlot D x jstar i)).val (nu i)) =
      (∏ i : {i // delta i = true},
        Erdos821.Blueprint.Analytic.mellin (wt i).val (nu i.val)) *
      (∏ i : {i // delta i = false},
        Erdos821.Blueprint.Analytic.mellin (ws i).val (nu i.val)) := by
  have hsplit := pureProduct_split (M := ℂ) D x jstar delta
    (fun i => Erdos821.Blueprint.Analytic.mellin
      ((fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)
        (Erdos821.S56Core.processedSlot D x jstar i)).val (nu i))
  rw [hsplit]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    have hval := ofTriple_take_val D x jstar hj hr delta ve wt ws i
    -- hval : ((ofTriple ...) ...).val = (wt i).val as ℕ; need mellin equality
    have heq : ((fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)
        (Erdos821.S56Core.processedSlot D x jstar i.val)).val = (wt i).val :=
      hval
    rw [heq]
  · apply Finset.prod_congr rfl
    intro i _
    have hval := ofTriple_skip_val D x jstar hj hr delta ve wt ws i
    have heq : ((fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)
        (Erdos821.S56Core.processedSlot D x jstar i.val)).val = (ws i).val :=
      hval
    rw [heq]

/-- Single-value coefficient with weight 1 is the membership indicator. -/
theorem singleCoeff_eq_indicator (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) (a : ℕ) :
    Erdos821.S56Core.productCoefficient
      (fun _ : Unit => D.SlotValue x jstar
        (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
      (fun _ v => v.val) (fun _ _ => (1 : ℂ)) a =
      if a ∈ D.slotValues x jstar
        (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) then 1 else 0 := by
  unfold Erdos821.S56Core.productCoefficient
  let hbij : (∀ _ : Unit,
      D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)) ≃
      D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) :=
    { toFun := fun f => f ()
      invFun := fun v _ => v
      left_inv := fun f => by funext u; cases u; rfl
      right_inv := fun v => rfl }
  have htrans : (∑ f : ∀ _ : Unit, D.SlotValue x jstar
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr),
      if (∏ _ : Unit, (f ()).val) = a then (∏ _ : Unit, (1 : ℂ)) else 0) =
      (∑ v : D.SlotValue x jstar
        (Erdos821.S56Core.exceptionalSlot D x jstar hj hr),
        if v.val = a then (1 : ℂ) else 0) := by
    apply Fintype.sum_equiv hbij
    intro f
    have hb : hbij f = f () := rfl
    simp [hb]
  rw [htrans]
  by_cases hmem : a ∈ D.slotValues x jstar
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)
  · obtain ⟨v0, hv0⟩ : ∃ v : D.SlotValue x jstar
        (Erdos821.S56Core.exceptionalSlot D x jstar hj hr), v.val = a :=
      ⟨⟨a, hmem⟩, rfl⟩
    have hsingle : (Finset.univ.filter
        (fun v : D.SlotValue x jstar
          (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) => v.val = a)) =
        {v0} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro heq
        apply Subtype.ext
        show v.val = v0.val
        rw [heq, hv0]
      · intro heq
        rw [Subtype.ext_iff.mp heq, hv0]
    have hsum : (∑ v : D.SlotValue x jstar
        (Erdos821.S56Core.exceptionalSlot D x jstar hj hr),
        if v.val = a then (1 : ℂ) else 0) = 1 := by
      rw [← Finset.sum_filter, hsingle, Finset.sum_singleton]
    rw [hsum]
    simp [hmem]
  · simp only [hmem, ite_false]
    apply Finset.sum_eq_zero
    intro v _
    split_ifs with heq
    · exfalso
      exact hmem (heq ▸ v.property)
    · rfl

/-- Residual index: exceptional (left) plus skip (right). -/
abbrev RIdx (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) :=
  Unit ⊕ {i : Erdos821.S56Core.ProcessedIndex D x jstar // delta i = false}

abbrev RA (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    : RIdx D x jstar delta → Type :=
  Sum.elim (fun _ : Unit => D.SlotValue x jstar
    (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
    (fun j : {i : Erdos821.S56Core.ProcessedIndex D x jstar // delta i = false} =>
      ProcessedValue D x jstar j.val)

def Rval (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool) :
    ∀ i : RIdx D x jstar delta, RA D x jstar hj hr delta i → ℕ :=
  fun i => match i with
  | Sum.inl _ => fun ve => ve.val
  | Sum.inr _ => fun ws => ws.val

def Rweight (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ) :
    ∀ i : RIdx D x jstar delta, RA D x jstar hj hr delta i → ℂ :=
  fun i => match i with
  | Sum.inl _ => fun _ => 1
  | Sum.inr j => fun ws => Erdos821.Blueprint.Analytic.mellin ws.val (nu j.val)

/-- Residual sum over exceptional + skip assignments. -/
def residualSum (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ)
    (t : ℕ) : ℂ :=
  ∑ p : (D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)) ×
      ((i : {i // delta i = false}) → ProcessedValue D x jstar i.val),
    if p.1.val * (∏ i, (p.2 i).val) = t then
      ∏ i, Erdos821.Blueprint.Analytic.mellin (p.2 i).val (nu i.val)
    else 0

/-- Product over a sum splits. -/
theorem prod_sum_split {M : Type*} [CommMonoid M]
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableEq (α ⊕ β)]
    (f : α ⊕ β → M) :
    (∏ i : α ⊕ β, f i) =
      (∏ a : α, f (Sum.inl a)) * (∏ b : β, f (Sum.inr b)) :=
  Fintype.prod_sum_type f

set_option maxHeartbeats 1200000 in
/-- Product over residual indices equals the residual sum. -/
theorem productCoeff_R_eq_residual (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ)
    (t : ℕ) :
    Erdos821.S56Core.productCoefficient
      (RA D x jstar hj hr delta) (Rval D x jstar hj hr delta)
      (Rweight D x jstar hj hr delta nu) t =
      residualSum D x jstar hj hr delta nu t := by
  unfold Erdos821.S56Core.productCoefficient residualSum
  -- unit equiv (as in singleCoeff, with let for transparency)
  let unitEquiv : (∀ _ : Unit, D.SlotValue x jstar
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)) ≃
      D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) :=
    { toFun := fun f => f ()
      invFun := fun v _ => v
      left_inv := fun f => by funext u; cases u; rfl
      right_inv := fun v => rfl }
  let e : (∀ i : RIdx D x jstar delta, RA D x jstar hj hr delta i) ≃
      ((D.SlotValue x jstar (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)) ×
        ((i : {i // delta i = false}) → ProcessedValue D x jstar i.val)) :=
    (Equiv.sumPiEquivProdPi (RA D x jstar hj hr delta)).trans
      (Equiv.prodCongr unitEquiv (Equiv.refl _))
  apply Fintype.sum_equiv e
  intro w
  have hprod_val : (∏ i : RIdx D x jstar delta,
      Rval D x jstar hj hr delta i (w i)) =
      (e w).1.val * (∏ i : {i // delta i = false}, ((e w).2 i).val) := by
    have hsplit := prod_sum_split (M := ℕ)
      (fun i : RIdx D x jstar delta => Rval D x jstar hj hr delta i (w i))
    have hunit : (∏ _ : Unit,
        Rval D x jstar hj hr delta (Sum.inl ()) (w (Sum.inl ()))) =
        (e w).1.val := by
      rw [Fintype.prod_unique]
      rfl
    have hskip : (∏ i : {i // delta i = false},
        Rval D x jstar hj hr delta (Sum.inr i) (w (Sum.inr i))) =
        (∏ i : {i // delta i = false}, ((e w).2 i).val) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl
    rw [hsplit, hunit, hskip]
  have hprod_weight : (∏ i : RIdx D x jstar delta,
      Rweight D x jstar hj hr delta nu i (w i)) =
      ∏ i : {i // delta i = false},
        Erdos821.Blueprint.Analytic.mellin (((e w).2 i).val) (nu i.val) := by
    have hsplit := prod_sum_split (M := ℂ)
      (fun i : RIdx D x jstar delta => Rweight D x jstar hj hr delta nu i (w i))
    have hunit : (∏ _ : Unit,
        Rweight D x jstar hj hr delta nu (Sum.inl ()) (w (Sum.inl ()))) = 1 := by
      rw [Fintype.prod_unique]
      rfl
    have hskip : (∏ i : {i // delta i = false},
        Rweight D x jstar hj hr delta nu (Sum.inr i) (w (Sum.inr i))) =
        (∏ i : {i // delta i = false},
          Erdos821.Blueprint.Analytic.mellin (((e w).2 i).val) (nu i.val)) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl
    rw [hsplit, hunit, hskip, one_mul]
  rw [hprod_val, hprod_weight]

set_option maxHeartbeats 1200000 in
/-- Residual sum equals the rough core with skip coefficients. -/
theorem residualSum_eq_roughCore (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ)
    (t : ℕ) :
    residualSum D x jstar hj hr delta nu t =
      Erdos821.S56Core.roughCore x (Real.exp (D.c₁ * D.scale x jstar))
        (Real.exp (D.c₂ * D.scale x jstar)) 0
        (processedCoefficient D x jstar delta false nu) t := by
  have hR := productCoeff_R_eq_residual D x jstar hj hr delta nu t
  rw [← hR]
  -- Split the residual product into exceptional × skip via the generic
  -- sum convolution on `Unit ⊕ skip` (no subtype transports).
  have hvalA : ∀ (_ : Unit) (a : D.SlotValue x jstar
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr)), 0 < a.val := by
    intro _ a
    have hmem : a.val ∈ D.slotValues x jstar
        (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) := a.property
    have hmem' : a.val ∈
        (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x jstar)⌉₊
          ⌊Real.exp (D.c₂ * D.scale x jstar)⌋₊).filter (rough (W x)) := by
      have heq := slotValues_exc D x jstar hj hr
      exact Eq.subst (motive := fun (tt : Finset ℕ) => a.val ∈ tt) heq hmem
    have hlo : ⌈Real.exp (D.c₁ * D.scale x jstar)⌉₊ ≤ a.val :=
      (Finset.mem_filter.mp hmem').1 |> Finset.mem_Icc.mp |>.1
    have hexp : (0 : ℝ) < Real.exp (D.c₁ * D.scale x jstar) := Real.exp_pos _
    have hceil : (0 : ℝ) < (⌈Real.exp (D.c₁ * D.scale x jstar)⌉₊ : ℕ) := by
      rw [Nat.cast_pos]
      exact Nat.ceil_pos.mpr hexp
    have hpos : (0 : ℝ) < (a.val : ℝ) :=
      lt_of_lt_of_le hceil (Nat.cast_le.mpr hlo)
    exact_mod_cast hpos
  have hvalB : ∀ (j : {i : Erdos821.S56Core.ProcessedIndex D x jstar // delta i = false})
      (b : ProcessedValue D x jstar j.val), 0 < b.val := by
    intro j b
    have hmem : b.val ∈ D.band x
        (Erdos821.S56Core.processedSlot D x jstar j.val).1.val := b.property
    have hprime : b.val.Prime := (Finset.mem_filter.mp hmem).2
    exact hprime.pos
  have hConv := Erdos821.P6Sum.sumCoefficientTask_proof
    (ι := Unit)
    (κ := {i : Erdos821.S56Core.ProcessedIndex D x jstar // delta i = false})
    (A := fun _ : Unit => D.SlotValue x jstar
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
    (B := fun j : {i : Erdos821.S56Core.ProcessedIndex D x jstar // delta i = false} =>
      ProcessedValue D x jstar j.val)
    (valA := fun _ v => v.val) (valB := fun _ q => q.val)
    (weightA := fun _ _ => (1 : ℂ))
    (weightB := fun j w => Erdos821.Blueprint.Analytic.mellin w.val (nu j.val))
    hvalA hvalB t
  -- Transport the convolution across the definitional identification of
  -- `RA/Rval/Rweight` with the `Sum.elim` family.
  have hTrans : Erdos821.S56Core.productCoefficient
      (RA D x jstar hj hr delta) (Rval D x jstar hj hr delta)
      (Rweight D x jstar hj hr delta nu) t =
      (∑ pr ∈ t.divisorsAntidiagonal,
        Erdos821.S56Core.productCoefficient
          (fun _ : Unit => D.SlotValue x jstar
            (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
          (fun _ v => v.val) (fun _ _ => (1 : ℂ)) pr.1 *
        Erdos821.S56Core.productCoefficient
          (fun j : {i : Erdos821.S56Core.ProcessedIndex D x jstar // delta i = false} =>
            ProcessedValue D x jstar j.val)
          (fun _ q => q.val)
          (fun j w => Erdos821.Blueprint.Analytic.mellin w.val (nu j.val)) pr.2) := by
    convert hConv using 1 <;> congr 1 <;> funext i <;> cases i <;> rfl
  rw [hTrans]
  -- Exceptional factor is the membership indicator (proved above).
  have hA : ∀ a : ℕ,
      Erdos821.S56Core.productCoefficient
        (fun _ : Unit => D.SlotValue x jstar
          (Erdos821.S56Core.exceptionalSlot D x jstar hj hr))
        (fun _ v => v.val) (fun _ _ => (1 : ℂ)) a =
      (if a ∈ D.slotValues x jstar
        (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) then (1 : ℂ) else 0) :=
    fun a => singleCoeff_eq_indicator D x jstar hj hr a
  -- Skip factor is the processed coefficient by definition.
  have hB : ∀ b : ℕ,
      Erdos821.S56Core.productCoefficient
        (fun j : {i : Erdos821.S56Core.ProcessedIndex D x jstar // delta i = false} =>
          ProcessedValue D x jstar j.val)
        (fun _ q => q.val)
        (fun j w => Erdos821.Blueprint.Analytic.mellin w.val (nu j.val)) b =
      processedCoefficient D x jstar delta false nu b :=
    fun _ => rfl
  simp_rw [hA, hB]
  -- The resulting divisor sum is `roughCore` by definition.
  unfold Erdos821.S56Core.roughCore
  apply Finset.sum_congr rfl
  intro pr _
  have hmem := mem_slotValues_exc_iff D x jstar hj hr pr.1
  simp only [hmem, mellin_zero, ite_mul, one_mul, zero_mul]

/-- Separating the take assignments factors the exact finite list sum. -/
theorem listCoefficient_split (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : Erdos821.S56Core.ProcessedIndex D x jstar → Bool)
    (nu : Erdos821.S56Core.ProcessedIndex D x jstar → ℝ)
    (e t : ℕ) (he : 0 < e) (M : ℂ) :
    (∑ z : D.Lists x jstar,
      if D.listProduct z = e * t ∧
          Erdos821.S56Core.processedFactor D z delta = e then
        M * ∏ i, Erdos821.Blueprint.Analytic.mellin
          (z (Erdos821.S56Core.processedSlot D x jstar i)).val (nu i)
      else 0) =
    processedCoefficient D x jstar delta true nu e * M *
      residualSum D x jstar hj hr delta nu t := by
  let T := (i : {i // delta i = true}) → ProcessedValue D x jstar i.val
  let R := D.SlotValue x jstar
      (Erdos821.S56Core.exceptionalSlot D x jstar hj hr) ×
      ((i : {i // delta i = false}) → ProcessedValue D x jstar i.val)
  let reindex : (T × R) ≃ D.Lists x jstar :=
    { toFun := fun p => (tripleEquiv D x jstar hj hr delta).symm
        (p.2.1, p.1, p.2.2)
      invFun := fun z =>
        let p := tripleEquiv D x jstar hj hr delta z
        (p.2.1, p.1, p.2.2)
      left_inv := fun p => by
        simp only [Equiv.apply_symm_apply, Prod.mk.eta]
      right_inv := fun z => by
        simp only [Prod.mk.eta, Equiv.symm_apply_apply] }
  calc
    _ = ∑ p : T × R,
        (if (∏ i, (p.1 i).val) = e then
          ∏ i, Erdos821.Blueprint.Analytic.mellin (p.1 i).val (nu i.val)
        else 0) * M *
        (if p.2.1.val * (∏ i, (p.2.2 i).val) = t then
          ∏ i, Erdos821.Blueprint.Analytic.mellin (p.2.2 i).val (nu i.val)
        else 0) := by
      symm
      apply Fintype.sum_equiv reindex
      rintro ⟨wt, ve, ws⟩
      change _ = if D.listProduct
          (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s) = e * t ∧
          Erdos821.S56Core.processedFactor D
            (fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s) delta = e then
          M * ∏ i, Erdos821.Blueprint.Analytic.mellin
            ((fun s => ofTriple D x jstar hj hr delta (ve, wt, ws) s)
              (Erdos821.S56Core.processedSlot D x jstar i)).val (nu i)
        else 0
      rw [listProduct_ofTriple, processedFactor_ofTriple, mellinProd_ofTriple]
      by_cases hw : (∏ i, (wt i).val) = e
      · have hc : ve.val * (∏ i, (wt i).val) * (∏ i, (ws i).val) = e * t ↔
            ve.val * (∏ i, (ws i).val) = t := by
          rw [hw]
          have hh : ve.val * e * (∏ i, (ws i).val) =
              e * (ve.val * (∏ i, (ws i).val)) := by ring
          rw [hh]
          exact Nat.mul_left_cancel_iff he
        simp only [hc]
        by_cases hs : ve.val * (∏ i, (ws i).val) = t
        · simp only [hw, hs, and_self, ite_true]
          ring
        · simp only [hw, hs, and_true, ite_true, ite_false, mul_zero]
      · simp only [hw, and_false, ite_false, zero_mul]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      unfold processedCoefficient Erdos821.S56Core.productCoefficient residualSum
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rfl

/-- Main split: exact finite coefficient factorization. -/
theorem SlotCoefficientSplitTask_proof : SlotCoefficientSplitTask := by
  intro D x jstar hj hr hdisj hrough delta nu u e hu he
  by_cases hdiv : e ∣ u
  · by_cases hfree : Erdos821.S56Core.GroupFree (D.groups x) e
    · -- e ∣ u and GroupFree: main identity via triple equiv + residual = roughCore
      have hFu_eq : groupFreePart (D.groups x) u =
          e * groupFreePart (D.groups x) (u / e) :=
        Erdos821.S56Core.groupFreePart_divisor_mul _ u e hu he hdiv hfree
      have hM_eq : markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u =
          markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) (u / e) :=
        Erdos821.S56Core.markWeight_divisor _ u e hdiv hfree _ _
      rw [if_pos hdiv, hFu_eq, hM_eq]
      rw [listCoefficient_split D x jstar hj hr delta nu e
        (groupFreePart (D.groups x) (u / e)) he]
      rw [residualSum_eq_roughCore]
    · -- e ∣ u but not GroupFree: both sides 0 (takeCoeff vanishes, LHS empty)
      have hLHS : (∑ z : D.Lists x jstar,
          if D.listProduct z = groupFreePart (D.groups x) u ∧
            Erdos821.S56Core.processedFactor D z delta = e then
            (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℂ) *
              ∏ i, Erdos821.Blueprint.Analytic.mellin
                (z (Erdos821.S56Core.processedSlot D x jstar i)).val (nu i)
          else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        have hfree_z := processedFactor_GroupFree D x jstar hdisj z delta
        have hne : Erdos821.S56Core.processedFactor D z delta ≠ e := by
          intro heq
          exact hfree (heq ▸ hfree_z)
        have hcond : ¬(D.listProduct z = groupFreePart (D.groups x) u ∧
            Erdos821.S56Core.processedFactor D z delta = e) := by
          intro hcon
          exact hne hcon.2
        simp [hcond]
      have hRHS_take : processedCoefficient D x jstar delta true nu e = 0 :=
        takeCoeff_eq_zero_of_not_GroupFree D x jstar hdisj delta nu e hfree
      simp [hdiv, hLHS, hRHS_take]
  · -- ¬(e ∣ u): both sides 0 (LHS empty via dvd_trans, RHS via if_neg)
    have hLHS : (∑ z : D.Lists x jstar,
        if D.listProduct z = groupFreePart (D.groups x) u ∧
          Erdos821.S56Core.processedFactor D z delta = e then
          (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℂ) *
            ∏ i, Erdos821.Blueprint.Analytic.mellin
              (z (Erdos821.S56Core.processedSlot D x jstar i)).val (nu i)
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      have hdvd : Erdos821.S56Core.processedFactor D z delta ∣ D.listProduct z :=
        processedFactor_dvd_listProduct D x jstar hj hr z delta
      have hFu_dvd : groupFreePart (D.groups x) u ∣ u :=
        Erdos821.S56Core.groupFreePart_dvd _ u hu
      by_cases hcon : D.listProduct z = groupFreePart (D.groups x) u ∧
          Erdos821.S56Core.processedFactor D z delta = e
      · exfalso
        obtain ⟨hlist, htake⟩ := hcon
        have he_dvd_Fu : e ∣ groupFreePart (D.groups x) u := by
          rw [← htake, ← hlist]
          exact hdvd
        exact hdiv (he_dvd_Fu.trans hFu_dvd)
      · simp [hcon]
    simp [hdiv, hLHS]

/-- The proof has exactly the lead task's frozen type. -/
example : Erdos821.S56Core.SlotCoefficientSplitTask := SlotCoefficientSplitTask_proof


end Erdos821.P6Split
