import Erdos821.P6Off.Dyadic

noncomputable section
open scoped BigOperators

namespace Erdos821.P6Off

/-- A fixed dyadic cutoff reduces any larger positive integer truncation to
its literal support interval. -/
theorem sum_dyadic_support_interval (Z : ℝ) (hZ : 0 < Z) (N : ℕ) (hN : 2 * Z ≤ (N : ℝ))
    (psi : ℝ → ℂ) (hs : Function.support psi ⊆ Set.Icc (1 / 2) 2) (g : ℕ → ℂ) :
    (∑ z ∈ Finset.Icc 1 N, psi (z / Z) * g z) =
      ∑ z ∈ Finset.Icc ⌈(1 / 2 : ℝ) * Z⌉₊ ⌊2 * Z⌋₊, psi (z / Z) * g z := by
  have hlow : 1 ≤ ⌈(1 / 2 : ℝ) * Z⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hhigh : ⌊2 * Z⌋₊ ≤ N := Nat.floor_le_of_le hN
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨hzlo, hzhi⟩ := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨hlow.trans hzlo, hzhi.trans hhigh⟩
  · intro z hz hznot
    have hzero : psi (z / Z) = 0 := by
      by_contra hne
      have hrange := hs hne
      apply hznot
      refine Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr ?_, Nat.le_floor ?_⟩
      · exact (le_div_iff₀ hZ).mp hrange.1
      · exact (div_le_iff₀ hZ).mp hrange.2
    simp [hzero]

theorem dyadicCutoff_complex_support :
    Function.support (fun t => (dyadicCutoff t : ℂ)) ⊆ Set.Icc (1 / 2) 2 := by
  intro t ht
  apply dyadicCutoff_support
  intro hzero
  exact ht (by simp [hzero])


end Erdos821.P6Off
