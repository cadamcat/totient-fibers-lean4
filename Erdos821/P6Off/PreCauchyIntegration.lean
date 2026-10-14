import Erdos821.P6Off.PreCauchySeparation
import Erdos821.P5.Basic

noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem pairSum_integral {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (U V : ℝ) (H : ℕ → Ω → ℂ) (alpha beta : ℕ → ℂ)
    (hH : ∀ u, Integrable (H u) mu) :
    pairSum U V (fun u => ∫ y, H u y ∂mu) alpha beta =
      ∫ y, pairSum U V (fun u => H u y) alpha beta ∂mu := by
  have hterm (m n : ℕ) : Integrable (fun y =>
      if Odd (m*n) ∧ 1 < m*n then H ((m*n-1)/2) y*alpha m*beta n else 0) mu := by
    split_ifs
    · exact ((hH _).mul_const _).mul_const _
    · exact integrable_zero _ _ _
  unfold pairSum
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hterm m n))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum _ (fun n _ => hterm m n)]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs
  · rw [integral_mul_const, integral_mul_const]
  · simp

theorem pairSum_const_mul (U V : ℝ) (H alpha beta : ℕ → ℂ) (c : ℂ) :
    pairSum U V (fun u => c*H u) alpha beta = c*pairSum U V H alpha beta := by
  unfold pairSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> ring

theorem pairSum_mul_const (U V : ℝ) (H alpha beta : ℕ → ℂ) (c : ℂ) :
    pairSum U V (fun u => H u*c) alpha beta = pairSum U V H alpha beta*c := by
  simpa only [mul_comm] using pairSum_const_mul U V H alpha beta c

theorem pairSum_finsetSum {ι : Type*} (s : Finset ι) (U V : ℝ)
    (H : ι → ℕ → ℂ) (alpha beta : ℕ → ℂ) :
    pairSum U V (fun u => ∑ i ∈ s, H i u) alpha beta =
      ∑ i ∈ s, pairSum U V (H i) alpha beta := by
  unfold pairSum
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

def allocationAtomPhase (D : BandData) {x : ℝ} {jstar : ℕ} (z : D.Lists x jstar)
    (E : ℝ) (delta : ProcessedIndex D x jstar → Bool) (xi : ProcessedIndex D x jstar → ℝ) : ℂ :=
  e (Real.log E*∑ i, xi i/processedScale D x jstar i)*
    slotPhase D z (branchFrequency D x jstar delta xi)

theorem allocationAtomPhase_norm (D : BandData) {x : ℝ} {jstar : ℕ} (z : D.Lists x jstar)
    (E : ℝ) (delta : ProcessedIndex D x jstar → Bool) (xi : ProcessedIndex D x jstar → ℝ) :
    ‖allocationAtomPhase D z E delta xi‖ = 1 := by
  simp only [allocationAtomPhase, slotPhase, norm_mul, norm_prod, Erdos821.S56Core.norm_e,
    Erdos821.P5Core.norm_mellin, Finset.prod_const_one, mul_one]

theorem allocationAtomPhase_continuous (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (E : ℝ) (delta : ProcessedIndex D x jstar → Bool) :
    Continuous (allocationAtomPhase D z E delta) := by
  unfold allocationAtomPhase slotPhase branchFrequency Erdos821.S56.slotFrequency e
    Erdos821.Blueprint.Analytic.mellin
  fun_prop

theorem integrable_branch_atom (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (E : ℝ) (delta : ProcessedIndex D x jstar → Bool)
    (a : Bool → ℝ → ℂ) (ha : ∀ b, Integrable (a b)) :
    Integrable (fun xi => branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
      allocationAtomPhase D z E delta xi) :=
  (branch_coefficient_integrable _ a ha delta).mul_bdd
    (allocationAtomPhase_continuous D z E delta).aestronglyMeasurable
      (Eventually.of_forall (fun xi => (allocationAtomPhase_norm D z E delta xi).le))

theorem truncatedBranch_eq_atom_integral (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (E : ℝ) (delta : ProcessedIndex D x jstar → Bool)
    (a : Bool → ℝ → ℂ) :
    truncatedBranch (pureIndices D x jstar).card a (L x) (Real.log E)
      (processedLog D z) (processedScale D x jstar) delta =
    ∫ xi in {xi : ProcessedIndex D x jstar → ℝ | ∀ i, ‖xi i‖ ≤ L x},
      branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
        allocationAtomPhase D z E delta xi := by
  rw [truncatedBranch]
  simp only [truncatedTransition]
  rw [truncated_branch_fourier_identity]
  apply integral_congr_ae
  filter_upwards with xi
  rw [processed_phase_mellin]
  simp only [allocationAtomPhase, slotPhase, branchFrequency, mul_assoc]

def slotFrequencyValue (D : BandData) (x : ℝ) (jstar : ℕ) (emin E : ℝ) (u : ℕ)
    (delta : ProcessedIndex D x jstar → Bool) (xi : ProcessedIndex D x jstar → ℝ) : ℂ :=
  (factorialNormalization D x*markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℝ)*
    ∑ z : D.Lists x jstar,
      if D.listProduct z = groupFreePart (D.groups x) u ∧
        processedFactor D z delta ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊ then
        allocationAtomPhase D z E delta xi else 0

theorem integrable_branch_slot (D : BandData) (x : ℝ) (jstar : ℕ) (emin E : ℝ) (u : ℕ)
    (delta : ProcessedIndex D x jstar → Bool) (a : Bool → ℝ → ℂ)
    (ha : ∀ b, Integrable (a b)) :
    Integrable (fun xi => branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
      slotFrequencyValue D x jstar emin E u delta xi) := by
  simp only [slotFrequencyValue, Finset.mul_sum, mul_ite, mul_zero]
  apply integrable_finsetSum
  intro z _
  split_ifs
  · simpa only [mul_left_comm] using (integrable_branch_atom D z E delta a ha).const_mul
      (factorialNormalization D x*markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℝ)
  · exact integrable_zero _ _ _

theorem truncatedAllocatedWeight_eq_integral (D : BandData) (x : ℝ) (jstar : ℕ)
    (emin E : ℝ) (a : Bool → ℝ → ℂ) (ha : ∀ b, Integrable (a b)) (u : ℕ) :
    truncatedAllocatedWeight D x jstar emin E a u =
      ∑ delta : ProcessedIndex D x jstar → Bool,
        ∫ xi in {xi : ProcessedIndex D x jstar → ℝ | ∀ i, ‖xi i‖ ≤ L x},
          branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
            slotFrequencyValue D x jstar emin E u delta xi := by
  let c : ℂ := (factorialNormalization D x*markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℝ)
  let P := fun (z : D.Lists x jstar) (delta : ProcessedIndex D x jstar → Bool) =>
    D.listProduct z = groupFreePart (D.groups x) u ∧ processedFactor D z delta ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊
  have hleft : truncatedAllocatedWeight D x jstar emin E a u =
      ∑ delta : ProcessedIndex D x jstar → Bool, ∑ z : D.Lists x jstar,
        if P z delta then c*truncatedBranch (pureIndices D x jstar).card a (L x) (Real.log E)
          (processedLog D z) (processedScale D x jstar) delta else 0 := by
    unfold truncatedAllocatedWeight truncatedAllocationMass
    rw [Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : D.listProduct z = groupFreePart (D.groups x) u
    · simp only [hz, ite_true, Finset.mul_sum, P, true_and, mul_ite, mul_zero, c]
    · simp [hz, P]
  rw [hleft]
  apply Finset.sum_congr rfl
  intro delta _
  have hi (z : D.Lists x jstar) : Integrable (fun xi =>
      if P z delta then c*(branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
        allocationAtomPhase D z E delta xi) else 0) := by
    split_ifs
    · exact (integrable_branch_atom D z E delta a ha).const_mul c
    · exact integrable_zero _ _ _
  have hid : (fun xi => branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
        slotFrequencyValue D x jstar emin E u delta xi) =
      (fun xi => ∑ z : D.Lists x jstar, if P z delta then
        c*(branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
          allocationAtomPhase D z E delta xi) else 0) := by
    funext xi
    simp only [slotFrequencyValue, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp only [c, P] at * <;> ring
  rw [hid, integral_finsetSum _ (fun z _ => (hi z).integrableOn)]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs with hp
  · rw [integral_const_mul, ← truncatedBranch_eq_atom_integral]
  · simp

theorem cutoff_mellin_phase (x : ℝ) (u : ℕ) (t : ℝ) :
    e (-t*Real.log x)*Erdos821.Blueprint.Analytic.mellin u (2*Real.pi*t) =
      e (t*(Real.log (u:ℝ)-Real.log x)) := by
  unfold e Erdos821.Blueprint.Analytic.mellin
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem slotBranchValue_as_frequency (D : BandData) (x : ℝ) (jstar : ℕ) (Cs K0 U V : ℝ)
    (alpha beta : ℕ → ℂ) (delta : ProcessedIndex D x jstar → Bool)
    (xi : ProcessedIndex D x jstar → ℝ) (t : ℝ) :
    slotBranchValue D x jstar Cs K0 U V alpha beta delta xi t =
      pairSum U V (fun u => e (t*(Real.log (u:ℝ)-Real.log x))*
        slotFrequencyValue D x jstar (U*L x^(-K0)*L x^(-Cs)) (U*L x^(-K0)) u delta xi) alpha beta := by
  unfold slotBranchValue slotFrequencyValue allocationAtomPhase
  dsimp only
  simp only [pairSum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs
  · simp only [Complex.ofReal_mul, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs
    · rw [← cutoff_mellin_phase]
      ring
    · ring
  · ring

theorem preCauchyExpansion_eq_pairSum (hsplit : SlotCoefficientSplitTask)
    (D : BandData) (x : ℝ) (jstar : ℕ) (Cs K0 U V : ℝ)
    (a : Bool → ℝ → ℂ) (f : ℝ → ℂ) (alpha beta : ℕ → ℂ)
    (ha : ∀ b, Integrable (a b)) (hf : Integrable f)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (hdisjoint : ∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g))
    (hfree : ∀ p : ℕ, rough (W x) p → GroupFree (D.groups x) p)
    (hepos : ∀ e ∈ Finset.Icc ⌈U*L x^(-K0)*L x^(-Cs)⌉₊ ⌊U*L x^(-K0)⌋₊, 0 < e) :
    preCauchyExpansion D x jstar Cs K0 U V a f alpha beta =
      pairSum U V (fun u => truncatedAllocatedWeight D x jstar
        (U*L x^(-K0)*L x^(-Cs)) (U*L x^(-K0)) a u*truncatedCutoff f (L x) x u) alpha beta := by
  let E := U*L x^(-K0)
  let emin := E*L x^(-Cs)
  let box := {xi : ProcessedIndex D x jstar → ℝ | ∀ i, ‖xi i‖ ≤ L x}
  let ball := {t : ℝ | ‖t‖ ≤ L x}
  have hi (u : ℕ) : Integrable (fun t => f t*e (t*(Real.log (u:ℝ)-Real.log x))) := by
    have hp : Continuous (fun t : ℝ => e (t*(Real.log (u:ℝ)-Real.log x))) := by unfold e; fun_prop
    exact hf.mul_bdd hp.aestronglyMeasurable
      (Eventually.of_forall (fun _ => (Erdos821.S56Core.norm_e _).le))
  have hinner (delta : ProcessedIndex D x jstar → Bool) (xi : ProcessedIndex D x jstar → ℝ) :
      (∫ t in ball, f t*branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t) =
        pairSum U V (fun u => slotFrequencyValue D x jstar emin E u delta xi*truncatedCutoff f (L x) x u) alpha beta := by
    simp_rw [branchSeparatedValue_eq_slotBranchValue hsplit D x jstar Cs K0 U V alpha beta delta xi
      _ hj hr hdisjoint hfree hepos, slotBranchValue_as_frequency]
    simp_rw [← pairSum_const_mul]
    rw [← pairSum_integral (volume.restrict ball) U V
      (fun u t => f t*(e (t*(Real.log (u:ℝ)-Real.log x))*slotFrequencyValue D x jstar emin E u delta xi))
      alpha beta (fun u => by simpa only [IntegrableOn, mul_assoc] using
        ((hi u).mul_const (slotFrequencyValue D x jstar emin E u delta xi)).integrableOn (s := ball))]
    congr 1
    funext u
    rw [truncatedCutoff, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  have houter (delta : ProcessedIndex D x jstar → Bool) :
      (∫ xi in box, branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
        pairSum U V (fun u => slotFrequencyValue D x jstar emin E u delta xi*truncatedCutoff f (L x) x u) alpha beta) =
      pairSum U V (fun u =>
        (∫ xi in box, branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
          slotFrequencyValue D x jstar emin E u delta xi)*truncatedCutoff f (L x) x u) alpha beta := by
    simp_rw [← pairSum_const_mul]
    rw [← pairSum_integral (volume.restrict box) U V
      (fun u xi => branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
        (slotFrequencyValue D x jstar emin E u delta xi*truncatedCutoff f (L x) x u)) alpha beta
      (fun u => by simpa only [IntegrableOn, mul_assoc] using
        ((integrable_branch_slot D x jstar emin E u delta a ha).mul_const (truncatedCutoff f (L x) x u)).integrableOn (s := box))]
    congr 1
    funext u
    simp only [← mul_assoc, integral_mul_const]
  change (∑ delta : ProcessedIndex D x jstar → Bool, ∫ xi in box,
    branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
      ∫ t in ball, f t*branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t) = _
  simp_rw [hinner, houter]
  rw [← pairSum_finsetSum]
  congr 1
  funext u
  rw [← Finset.sum_mul, ← truncatedAllocatedWeight_eq_integral D x jstar emin E a ha u]


end Erdos821.P6Off
