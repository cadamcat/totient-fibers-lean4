import Erdos821.P7.FreeWindowTask

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Free
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P7Core

theorem prime_window_subset_band (D : BandData) (x a b y : ℝ)
    (hlo : Real.exp (D.c₁ * D.scale x 0) ≤ a * y)
    (hhi : b * y ≤ Real.exp (D.c₂ * D.scale x 0))
    (hby : 0 ≤ b * y) :
    (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime ⊆ D.band x 0 := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hrange := Finset.mem_Icc.mp hp'.1
  have hpLo : a * y ≤ (p : ℝ) := Nat.ceil_le.mp hrange.1
  have hpHi : (p : ℝ) ≤ b * y := (Nat.le_floor_iff hby).mp hrange.2
  have hpPrime : p.Prime := hp'.2
  unfold BandData.band
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.ceil_le.mpr (hlo.trans hpLo)
    · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr (hpHi.trans hhi)
  · exact hpPrime

theorem prime_mem_window_of_real_bounds (p : ℕ) (a b y : ℝ)
    (hp : p.Prime) (hlo : a * y ≤ (p : ℝ))
    (hhi : (p : ℝ) ≤ b * y) (hby : 0 ≤ b * y) :
    p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    exact ⟨Nat.ceil_le.mpr hlo, (Nat.le_floor_iff hby).mpr hhi⟩
  · exact hp

end Erdos821.P7Free
