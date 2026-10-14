import Erdos821.S56.Tasks
import Erdos821.S56.BandSize

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem markWeight_nonneg (G : PrimeGroups) (q : ℝ) (hq : 0 ≤ q)
    (t : Fin G.size → ℕ) (n : ℕ) : 0 ≤ markWeight G q t n := by
  unfold markWeight
  apply mul_nonneg (zpow_nonneg hq _)
  apply Finset.prod_nonneg
  intro g _
  have hm : 0 ≤ mass G g := Finset.sum_nonneg (fun p _ => by positivity)
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg hm _)

/-- The finite Rankin inequality has no summability premise. -/
theorem rankin_tail_bound (s : Finset ℕ) (w : ℕ → ℝ)
    (hs : ∀ n ∈ s, 0 < n) (hw : ∀ n ∈ s, 0 ≤ w n)
    (Y theta : ℝ) (hY : 0 < Y) (htheta : 0 < theta) :
    (∑ n ∈ s, if Y < (n : ℝ) then w n / n else 0) ≤
      Y ^ (-theta) * ∑ n ∈ s, w n / (n : ℝ) ^ (1 - theta) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hp : (0 : ℝ) < n := by exact_mod_cast hs n hn
  by_cases hlarge : Y < (n : ℝ)
  · rw [ite_eq_left hlarge]
    have hbase : (n : ℝ) ^ (-theta) ≤ Y ^ (-theta) :=
      Real.rpow_le_rpow_of_nonpos hY hlarge.le (by linarith)
    have heq : w n / n = (n : ℝ) ^ (-theta) *
        (w n / (n : ℝ) ^ (1 - theta)) := by
      calc
        _ = w n * (n : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; rfl
        _ = w n * ((n : ℝ) ^ (-theta) * (n : ℝ) ^ (-(1 - theta))) := by
          rw [← Real.rpow_add hp]
          congr 2
          ring
        _ = _ := by rw [Real.rpow_neg hp.le (1 - theta)]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hbase
      (div_nonneg (hw n hn) (Real.rpow_nonneg hp.le _))
  · rw [ite_eq_right hlarge]
    exact mul_nonneg (Real.rpow_nonneg hY.le _) (div_nonneg (hw n hn)
      (Real.rpow_nonneg hp.le _))

theorem rankin_log_identity (x sigma d : ℝ) (hx : 1 < x) :
    (x ^ sigma) ^ (-(L x ^ (-d))) =
      Real.exp (-sigma * L x ^ (1 - d)) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hL : 0 < L x := Real.log_pos hx
  rw [← Real.rpow_mul hxpos.le, Real.rpow_def_of_pos hxpos]
  have hpow : L x ^ (1 - d) = L x * L x ^ (-d) := by
    rw [sub_eq_add_neg, Real.rpow_add hL, Real.rpow_one]
  rw [hpow]
  congr 1
  unfold L
  ring

/-- The only analytic input here is the explicitly named tilted mass task.
The conversion to the paper's group-prime tail is exact. -/
theorem group_tail_of_tilted (hMass : TiltedGroupMassTask)
    (P : Geometry) (sigma : ℝ) (_hsigma : 0 < sigma) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ G : PrimeGroups, Admissible P x G → ∀ N : ℕ,
        (∑ v ∈ Finset.Icc 1 N,
          if groupFreePart G v = 1 ∧ x ^ sigma < (v : ℝ) then
            markWeight G P.q (fun _ => P.ell) v / v else 0) ≤
          Real.exp (-sigma * L x ^ (1 - P.d)) * L x ^ C := by
  obtain ⟨C, hevent⟩ := hMass P
  refine ⟨C, ?_⟩
  filter_upwards [hevent, eventually_gt_atTop 1] with x hx hx1
  intro G hG N
  let w : ℕ → ℝ := fun v => if groupFreePart G v = 1 then
    markWeight G P.q (fun _ => P.ell) v else 0
  have hw (v : ℕ) : 0 ≤ w v := by
    dsimp [w]
    split_ifs
    · exact markWeight_nonneg G P.q P.damping.1.le _ v
    · exact le_rfl
  have htail := rankin_tail_bound (Finset.Icc 1 N) w
    (fun v hv => Nat.zero_lt_of_lt (Finset.mem_Icc.mp hv).1)
    (fun v _ => hw v) (x ^ sigma) (L x ^ (-P.d))
    (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _) (Real.rpow_pos_of_pos (Real.log_pos hx1) _)
  have hmass' : (∑ v ∈ Finset.Icc 1 N, w v / (v : ℝ) ^ (1 - L x ^ (-P.d))) ≤
      L x ^ C := by
    simpa only [w, ite_div, zero_div] using hx G hG N
  have hfinal := htail.trans (mul_le_mul_of_nonneg_left hmass'
    (Real.rpow_nonneg (Real.rpow_nonneg (le_of_lt (zero_lt_one.trans hx1)) _) _))
  rw [rankin_log_identity x sigma P.d hx1] at hfinal
  convert hfinal using 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases hp : groupFreePart G v = 1 <;> by_cases hcut : x ^ sigma < (v : ℝ) <;>
    simp [w, hp, hcut]


end Erdos821.S56Core
