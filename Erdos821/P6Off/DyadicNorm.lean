import Erdos821.P6Off.Dyadic

namespace Erdos821.P6Off

theorem abs_dyadicCutoff_le_one (t : ℝ) : |dyadicCutoff t| ≤ 1 := by
  unfold dyadicCutoff dyadicStep
  by_cases ht : t ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  · have hmono : Real.smoothTransition (2 * (t / 2) - 1) ≤
        Real.smoothTransition (2 * t - 1) := Real.smoothTransition.monotone (by linarith)
    have hnonneg : 0 ≤ Real.smoothTransition (2 * t - 1) -
        Real.smoothTransition (2 * (t / 2) - 1) := sub_nonneg.mpr hmono
    rw [abs_of_nonneg hnonneg]
    linarith [Real.smoothTransition.nonneg (2 * (t / 2) - 1),
      Real.smoothTransition.le_one (2 * t - 1)]


end Erdos821.P6Off
