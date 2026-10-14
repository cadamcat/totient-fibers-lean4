import Erdos821.Blueprint.Candidate

noncomputable section

namespace Erdos821.P7Core
open Erdos821.Blueprint

theorem band_upper_lt_lower (D : BandData) (x : ℝ)
    (hc₁ : D.c₁ = 1) (hc₂ : D.c₂ = 6 / 5) (hratio : D.ratio = 2)
    (hscale : 0 < D.s' * Analytic.L x) {i j : ℕ} (hij : i < j) :
    Real.exp (D.c₂ * D.scale x j) < Real.exp (D.c₁ * D.scale x i) := by
  have hpow : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hij)
  have hscale' : D.scale x j ≤ D.scale x i / 2 := by
    have h := div_le_div_of_nonneg_left hscale.le
      (pow_pos (show (0 : ℝ) < 2 by norm_num) (i + 1)) hpow
    simpa only [BandData.scale, hratio, pow_succ, div_div] using h
  have hi : 0 < D.scale x i := by
    dsimp [BandData.scale]
    rw [hratio]
    exact div_pos hscale (by positivity)
  apply Real.exp_lt_exp.mpr
  rw [hc₁, hc₂, one_mul]
  nlinarith

theorem bands_disjoint (D : BandData) (x : ℝ)
    (hc₁ : D.c₁ = 1) (hc₂ : D.c₂ = 6 / 5) (hratio : D.ratio = 2)
    (hscale : 0 < D.s' * Analytic.L x) (i j : ℕ) (hij : i ≠ j) :
    Disjoint (D.band x i) (D.band x j) := by
  classical
  have hordered : ∀ i j : ℕ, i < j → Disjoint (D.band x i) (D.band x j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hpi' := Finset.mem_Icc.mp (Finset.mem_filter.mp hpi).1
    have hpj' := Finset.mem_Icc.mp (Finset.mem_filter.mp hpj).1
    have hlo : Real.exp (D.c₁ * D.scale x i) ≤ (p : ℝ) :=
      Nat.le_of_ceil_le hpi'.1
    have hhi : (p : ℝ) ≤ Real.exp (D.c₂ * D.scale x j) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mp hpj'.2
    exact (not_lt_of_ge (hlo.trans hhi))
      (band_upper_lt_lower D x hc₁ hc₂ hratio hscale hij)
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hordered i j hij
  · exact (hordered j i hji).symm

end Erdos821.P7Core

