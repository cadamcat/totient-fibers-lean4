import Erdos821.Blueprint.Candidate

noncomputable section
open scoped BigOperators

namespace Erdos821.P7Core
open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

theorem groupMass_nonneg (G : PrimeGroups) (g : Fin G.size) : 0 ≤ mass G g := by
  apply Finset.sum_nonneg
  intro p _
  exact div_nonneg zero_le_one (Nat.cast_nonneg p)

theorem markWeight_nonneg (G : PrimeGroups) (q : ℝ) (hq : 0 ≤ q)
    (t : Fin G.size → ℕ) (n : ℕ) : 0 ≤ markWeight G q t n := by
  unfold markWeight
  apply mul_nonneg (zpow_nonneg hq _)
  apply Finset.prod_nonneg
  intro g _
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (groupMass_nonneg G g) _)

theorem bandCoefficient_nonneg (D : BandData) (x : ℝ) (jstar v : ℕ) :
    0 ≤ D.aQ x jstar v := by
  unfold BandData.aQ
  positivity

theorem weighted_nonneg (C : CandidateData) (hq : 0 ≤ C.bands.geometry.q)
    (hpsi : ∀ y, 0 ≤ C.psi y) (x : ℝ) (jstar u : ℕ) :
    0 ≤ C.weighted x jstar u := by
  apply mul_nonneg _ (hpsi _)
  exact mul_nonneg (bandCoefficient_nonneg _ _ _ _)
    (markWeight_nonneg _ _ hq _ _)

theorem geometry_weighted_nonneg (C : CandidateData) (δ : ℝ) (hC : C.Geometry δ)
    (x : ℝ) (jstar u : ℕ) : 0 ≤ C.weighted x jstar u := by
  rcases hC with ⟨_, _, _, _, _, _, _, _, _, hq, _, _, _, _, _, _, _, _, _, _,
    _, _, hpsi, _⟩
  apply weighted_nonneg C _ hpsi x jstar u
  rw [hq]
  norm_num

theorem weighted_interval_support (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2)
    (x : ℝ) (hx : 0 < x) (jstar u : ℕ) (hu : C.weighted x jstar u ≠ 0) :
    x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x := by
  have hne : C.psi ((u : ℝ) / x) ≠ 0 := (mul_ne_zero_iff.mp hu).2
  have hmem := hpsi hne
  exact ⟨by linarith [(le_div_iff₀ hx).mp hmem.1],
    (div_le_iff₀ hx).mp hmem.2⟩

end Erdos821.P7Core

