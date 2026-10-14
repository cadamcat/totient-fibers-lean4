import Erdos821.S56.FixedFourier
import Erdos821.S56.BranchPartition
import Erdos821.S56.BranchRange

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core

def transitionWindow (R t : ℝ) : ℝ :=
  Real.smoothTransition (t + R + 1) * Real.smoothTransition (R + 1 - t)

def transition (R : ℝ) (b : Bool) (t : ℝ) : ℝ :=
  transitionWindow R t *
    if b then Real.smoothTransition t else 1 - Real.smoothTransition t

theorem window_bounds (R t : ℝ) :
    0 ≤ transitionWindow R t ∧ transitionWindow R t ≤ 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_le_one₀ (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem window_eq_one (R t : ℝ) (ht : |t| ≤ R) : transitionWindow R t = 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  unfold transitionWindow
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem transition_bounds (R t : ℝ) (b : Bool) :
    0 ≤ transition R b t ∧ transition R b t ≤ 1 := by
  obtain ⟨hρ, hρ1⟩ := window_bounds R t
  have hγ := Real.smoothTransition.nonneg t
  have hγ1 := Real.smoothTransition.le_one t
  cases b <;> simp only [transition, Bool.false_eq_true, ↓reduceIte]
  · constructor
    · exact mul_nonneg hρ (by linarith)
    · exact mul_le_one₀ hρ1 (by linarith) (by linarith)
  · exact ⟨mul_nonneg hρ hγ, mul_le_one₀ hρ1 hγ hγ1⟩

theorem transition_sum (R t : ℝ) :
    transition R false t + transition R true t = transitionWindow R t := by
  simp only [transition, Bool.false_eq_true, ↓reduceIte]
  ring

theorem transition_smooth (R : ℝ) (b : Bool) : ContDiff ℝ ∞ (transition R b) := by
  have hρ : ContDiff ℝ ∞ (transitionWindow R) := by
    unfold transitionWindow
    exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop))
  cases b
  · exact hρ.mul (contDiff_const.sub Real.smoothTransition.contDiff)
  · exact hρ.mul Real.smoothTransition.contDiff

theorem transition_support (R : ℝ) (b : Bool) :
    Function.support (transition R b) ⊆ Set.Icc (-R - 1) (R + 1) := by
  intro t ht
  have hnonzero : transition R b t ≠ 0 := ht
  have hleft : 0 < t + R + 1 := by
    by_contra h
    have hz := Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)
    simp [transition, transitionWindow, hz] at hnonzero
  have hright : 0 < R + 1 - t := by
    by_contra h
    have hz := Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)
    simp [transition, transitionWindow, hz] at hnonzero
  constructor <;> linarith

theorem transition_compact (R : ℝ) (b : Bool) : HasCompactSupport (transition R b) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (transition_support R b)

def clippedBranchMass (n : ℕ) (target : ℝ) (v s : Fin n → ℝ)
    (R : ℝ) (delta : Fin n → Bool) : ℝ :=
  ∏ i, transition R (delta i)
    ((Erdos821.S56.residual target v delta i.val - v i) / s i)

theorem clipped_branch_factorization (n : ℕ) (target : ℝ) (v s : Fin n → ℝ)
    (R : ℝ) (delta : Fin n → Bool) :
    clippedBranchMass n target v s R delta =
      (∏ i, transitionWindow R
        ((Erdos821.S56.residual target v delta i.val - v i) / s i)) *
        Erdos821.S56.branchMass target v s Real.smoothTransition delta := by
  simp only [clippedBranchMass, transition, Finset.prod_mul_distrib,
    Erdos821.S56.branchMass]

theorem clipped_branch_eq (n : ℕ) (target : ℝ) (v s : Fin n → ℝ) (R : ℝ)
    (delta : Fin n → Bool)
    (hrange : 0 < Erdos821.S56.branchMass target v s Real.smoothTransition delta →
      ∀ i, |(Erdos821.S56.residual target v delta i.val - v i) / s i| ≤ R) :
    clippedBranchMass n target v s R delta =
      Erdos821.S56.branchMass target v s Real.smoothTransition delta := by
  have hnonneg : 0 ≤ Erdos821.S56.branchMass target v s Real.smoothTransition delta := by
    unfold Erdos821.S56.branchMass
    apply Finset.prod_nonneg
    intro i _
    by_cases hd : delta i = true
    · simp only [hd, ↓reduceIte]
      exact Real.smoothTransition.nonneg _
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      linarith [Real.smoothTransition.le_one
        ((Erdos821.S56.residual target v delta i.val - v i) / s i)]
  rw [clipped_branch_factorization]
  by_cases hpos : 0 < Erdos821.S56.branchMass target v s Real.smoothTransition delta
  · have hprod : (∏ i, transitionWindow R
        ((Erdos821.S56.residual target v delta i.val - v i) / s i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      exact window_eq_one R _ (hrange hpos i)
    rw [hprod, one_mul]
  · have hz := le_antisymm (le_of_not_gt hpos) hnonneg
    rw [hz, mul_zero]

theorem clipped_branch_partition (n : ℕ) (target : ℝ) (v s : Fin n → ℝ) (R : ℝ)
    (hrange : ∀ delta, 0 < Erdos821.S56.branchMass target v s Real.smoothTransition delta →
      ∀ i, |(Erdos821.S56.residual target v delta i.val - v i) / s i| ≤ R) :
    (∑ delta : Fin n → Bool, clippedBranchMass n target v s R delta) = 1 := by
  simp_rw [clipped_branch_eq n target v s R _ (hrange _)]
  exact Erdos821.S56.branch_partition_proved n target v s Real.smoothTransition

/-- The same invariant controlling the terminal factor also bounds every
transition argument in a fixed compact interval. -/
theorem branch_argument_bound (n : ℕ) (target terminal R : ℝ) (v s : Fin n → ℝ)
    (ht : 0 ≤ target) (hterm : 0 ≤ terminal)
    (hinit : target ≤ (∑ i, v i) + terminal)
    (hv : ∀ i, 0 < v i ∧ 0 < s i)
    (hroom : ∀ i, v i + s i ≤
      (∑ t ∈ Finset.univ.filter (fun t : Fin n => i.val < t.val), v t) + terminal)
    (hcap : ∀ i, (∑ t ∈ Finset.univ.filter (fun t : Fin n => i.val ≤ t.val), v t) +
      terminal ≤ R * s i) :
    ∀ delta, 0 < Erdos821.S56.branchMass target v s Real.smoothTransition delta →
      ∀ i, |(Erdos821.S56.residual target v delta i.val - v i) / s i| ≤ R := by
  have hgamma : ∀ t, 0 ≤ Real.smoothTransition t ∧ Real.smoothTransition t ≤ 1 ∧
      (t ≤ 0 → Real.smoothTransition t = 0) ∧ (1 ≤ t → Real.smoothTransition t = 1) :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t,
      Real.smoothTransition.zero_of_nonpos, Real.smoothTransition.one_of_one_le⟩
  intro delta hmass i
  obtain ⟨hR0, hRhi⟩ := branch_prefix_bounds n target terminal v s Real.smoothTransition
    ht hterm hinit hv hgamma hroom delta hmass i.val i.isLt.le
  have hvi : v i ≤ (∑ t ∈ Finset.univ.filter (fun t : Fin n => i.val ≤ t.val), v t) :=
    Finset.single_le_sum (fun j _ => (hv j).1.le)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, le_rfl⟩)
  have hvmax : v i ≤ R * s i := by linarith [hcap i]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ (hv i).2).mpr
    linarith
  · apply (div_le_iff₀ (hv i).2).mpr
    linarith [(hRhi.trans (hcap i)), (hv i).1]


end Erdos821.S56Core
