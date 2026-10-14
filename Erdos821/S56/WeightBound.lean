import Erdos821.P6Slot.SlotMultiplicity
import Erdos821.P6Sq.EndpointSquareTask
import Erdos821.S56.CoreBound
import Erdos821.S56.BandSize

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem aQ_nonneg (D : BandData) (x : ℝ) (jstar v : ℕ) : 0 ≤ D.aQ x jstar v := by
  unfold BandData.aQ
  positivity

theorem band_weight_nonneg (D : BandData) (x : ℝ) (jstar u : ℕ) : 0 ≤ D.weight x jstar u :=
  mul_nonneg (aQ_nonneg D x jstar _) (markWeight_nonneg _ _ D.geometry.damping.1.le _ u)

theorem band_weight_bound (D : BandData) (hD : D.Valid) :
    ∃ C : ℝ, 0 < C ∧ ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop, ∀ u : ℕ,
      D.weight x jstar u ≤ L x ^ C * ((groupFreePart (D.groups x) u).divisors.card : ℝ) := by
  obtain ⟨C, hC, hmark⟩ := Erdos821.P6Sq.markWeight_log_bound D.geometry
  refine ⟨C, hC, ?_⟩
  intro jstar
  have hslot := Erdos821.P6Slot.slotMultiplicityTask_proof D hD jstar
  have hdata := hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, hcmin, hcmax, hevent⟩ := hdata
  filter_upwards [hslot, hmark, hevent] with x hx hm hvalid
  intro u
  have hm0 := markWeight_nonneg (D.groups x) D.geometry.q D.geometry.damping.1.le
    (fun _ => D.geometry.ell) u
  have ha0 := aQ_nonneg D x jstar (groupFreePart (D.groups x) u)
  have h := mul_le_mul (hx _) (hm (D.groups x) hvalid.1 u) hm0
    (Nat.cast_nonneg (groupFreePart (D.groups x) u).divisors.card :
      (0 : ℝ) ≤ (groupFreePart (D.groups x) u).divisors.card)
  simpa only [BandData.weight, mul_comm] using h

theorem band_weight_divisor_bound (D : BandData) (hD : D.Valid) :
    ∃ C : ℝ, 0 < C ∧ ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, 0 < u →
      D.weight x jstar u ≤ L x ^ C * (u.divisors.card : ℝ) := by
  obtain ⟨C, hC, hx⟩ := band_weight_bound D hD
  refine ⟨C, hC, ?_⟩
  intro jstar
  filter_upwards [hx jstar, tendsto_L.eventually (eventually_gt_atTop 0)] with x hx hL
  intro u hu
  have hcard : ((groupFreePart (D.groups x) u).divisors.card : ℝ) ≤ u.divisors.card := by
    exact_mod_cast Finset.card_le_card
      (Nat.divisors_subset_of_dvd hu.ne' (groupFreePart_dvd (D.groups x) u hu))
  exact (hx u).trans (mul_le_mul_of_nonneg_left hcard (Real.rpow_nonneg hL.le _))


end Erdos821.S56Core
