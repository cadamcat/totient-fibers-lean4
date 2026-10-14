import Erdos821.S56.SlotBounds

noncomputable section

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem band_endpoint_power (D : BandData) (x c : ℝ) (j : ℕ) (hx : 0 < x) :
    Real.exp (c*D.scale x j) = x^(c*D.s'/D.ratio^j) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  unfold BandData.scale L
  ring

theorem exceptional_exponents (D : BandData) (hD : D.Valid) (jstar : ℕ) :
    0 < D.c₁*D.s'/D.ratio^jstar ∧
    D.c₁*D.s'/D.ratio^jstar < D.c₂*D.s'/D.ratio^jstar ∧
    D.c₂*D.s'/D.ratio^jstar < 1/4 := by
  have hc1 := hD.2.1
  have hc12 := hD.2.2.1
  have hs := hD.2.2.2.1
  have hr := hD.2.2.2.2.1
  have heta := hD.2.2.2.2.2.1
  have hden : 0 < D.ratio^jstar := pow_pos (zero_lt_one.trans hr) _
  have hden1 : 1 ≤ D.ratio^jstar := one_le_pow₀ hr.le
  have hnum : 0 < D.c₂*D.s' := mul_pos (hc1.trans hc12) hs
  have hle : D.c₂*D.s'/D.ratio^jstar ≤ D.c₂*D.s' := by
    apply (div_le_iff₀ hden).mpr
    exact le_mul_of_one_le_right hnum.le hden1
  exact ⟨div_pos (mul_pos hc1 hs) hden,
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hc12 hs) hden, hle.trans_lt heta⟩


end Erdos821.S56Core
