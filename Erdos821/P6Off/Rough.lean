import Erdos821.P6Off.Determinant

noncomputable section
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- Every admissible group prime is below the roughness threshold once L≥1. -/
theorem group_prime_le_W (P : Geometry) (x : ℝ) (G : PrimeGroups)
    (hx : 1 ≤ L x) (hG : Admissible P x G)
    (g : Fin G.size) (p : ℕ) (hp : p ∈ G.primes g) : (p : ℝ) ≤ W x := by
  have hpd : (p : ℝ) ≤ Real.exp (L x ^ P.d) := by
    have hbound := hG.2.2.2.1 g p hp
    by_cases hg : g ∈ G.small
    · rw [if_pos hg] at hbound
      exact hbound.2.trans (Real.exp_le_exp.mpr
        (Real.rpow_le_rpow_of_exponent_le hx
          (le_of_lt (P.ordered.2.2.1.trans P.ordered.2.2.2.1))))
    · rw [if_neg hg] at hbound
      exact hbound.2
  apply hpd.trans
  apply Real.exp_le_exp.mpr
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith [P.ordered.2.2.2.2])

theorem rough_groupFree (P : Geometry) (x : ℝ) (G : PrimeGroups)
    (hx : 1 ≤ L x) (hG : Admissible P x G) (m : ℕ) (hm : rough (W x) m) :
    GroupFree G m := by
  intro p hp hpm
  obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
  exact (not_lt_of_ge (group_prime_le_W P x G hx hG g p hpg))
    (hm.2 p (G.prime g p hpg) hpm)

/-- The rough cutoff dominates every fixed logarithmic power. -/
theorem eventually_log_rpow_le_W (C : ℝ) : ∀ᶠ x : ℝ in atTop, L x ^ C ≤ W x := by
  have hsmall := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ))
    (by norm_num)).const_mul_left (max C 1)
  have hbound : ∀ᶠ t : ℝ in atTop, ‖max C 1 * Real.log t‖ ≤ ‖t ^ (1 / 2 : ℝ)‖ :=
    by simpa using hsmall.bound (c := 1) zero_lt_one
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hL.eventually hbound, hL.eventually (eventually_ge_atTop 1)] with x hb hx
  have hpos : 0 < L x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log (L x) := Real.log_nonneg hx
  have hc : C * Real.log (L x) ≤ Real.sqrt (L x) := by
    calc
      C * Real.log (L x) ≤ max C 1 * Real.log (L x) := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
      _ ≤ |max C 1 * Real.log (L x)| := le_abs_self _
      _ ≤ |L x ^ (1 / 2 : ℝ)| := hb
      _ = Real.sqrt (L x) := by rw [abs_of_pos (Real.rpow_pos_of_pos hpos _), Real.sqrt_eq_rpow]
  rw [Real.rpow_def_of_pos hpos, W]
  exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hc)


end Erdos821.P6Off
