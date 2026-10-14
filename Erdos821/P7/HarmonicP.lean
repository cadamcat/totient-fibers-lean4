import Erdos821.P7.Positivity
import Erdos821.P6Mass.Mass
import Erdos821.S56.Rankin
import Erdos821.S56.GeometricScales

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- A uniform bound on positive initial intervals also bounds all finite
subsets, hence the genuine infinite mass. -/
theorem summable_and_tsum_le_of_Icc (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0)
    (hB : ∀ N, (∑ n ∈ Finset.Icc 1 N, f n) ≤ B) :
    Summable f ∧ (∑' n, f n) ≤ B := by
  have hs (s : Finset ℕ) : (∑ n ∈ s, f n) ≤ B := by
    have heq : (∑ n ∈ s, f n) = ∑ n ∈ s.filter (fun n => 0 < n), f n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : 0 < n
      · simp [hn]
      · have hn0 : n = 0 := by omega
        simp [hn, hn0, hf0]
    have hsub : s.filter (fun n => 0 < n) ⊆ Finset.Icc 1 (s.sup id) := by
      intro n hn
      obtain ⟨hns, hn0⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨hn0, Finset.le_sup (f := id) hns⟩
    rw [heq]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)).trans (hB _)
  exact ⟨summable_of_sum_le hf hs, Real.tsum_le_of_sum_le hf hs⟩

def groupHarmonicTerm (P : Geometry) (G : PrimeGroups) (r : ℕ) : ℝ :=
  if 0 < r ∧ groupFreePart G r = 1 then
    markWeight G P.q (fun _ => P.ell) r / r else 0

theorem groupHarmonicTerm_nonneg (P : Geometry) (G : PrimeGroups) (r : ℕ) :
    0 ≤ groupHarmonicTerm P G r := by
  unfold groupHarmonicTerm
  split_ifs
  · exact div_nonneg (markWeight_nonneg G P.q P.damping.1.le _ _) (Nat.cast_nonneg _)
  · exact le_rfl

/-- The ordinary harmonic terms are dominated by the accepted tilted terms. -/
theorem harmonic_sum_le_tilted (P : Geometry) (G : PrimeGroups) (x : ℝ)
    (hL : 0 ≤ L x) (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 N, groupHarmonicTerm P G r) ≤
      ∑ r ∈ Finset.Icc 1 N, if groupFreePart G r = 1 then
        markWeight G P.q (fun _ => P.ell) r /
          (r : ℝ) ^ (1 - L x ^ (-P.d)) else 0 := by
  apply Finset.sum_le_sum
  intro r hr
  have hr0 : 0 < r := (Finset.mem_Icc.mp hr).1
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  by_cases hp : groupFreePart G r = 1
  · simp only [groupHarmonicTerm, hr0, hp, and_self, ite_true]
    have hpow : (r : ℝ) ^ (1 - L x ^ (-P.d)) ≤ r := by
      calc
        _ ≤ (r : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1
          (by linarith [Real.rpow_nonneg hL (-P.d)])
        _ = r := Real.rpow_one _
    exact div_le_div_of_nonneg_left (markWeight_nonneg G P.q P.damping.1.le _ _)
      (Real.rpow_pos_of_pos hrR _) hpow
  · simp [groupHarmonicTerm, hp]

/-- Summability and the polynomial upper bound are consequences of the finite
tilted mass estimate; no convention for divergent tsums is used. -/
theorem group_harmonic_summable_polylog (P : Geometry) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ G : PrimeGroups, Admissible P x G →
      Summable (groupHarmonicTerm P G) ∧
        (∑' r, groupHarmonicTerm P G r) ≤ L x ^ C := by
  obtain ⟨C, he⟩ := Erdos821.P6Mass.TiltedGroupMassTask_proof P
  refine ⟨C, ?_⟩
  filter_upwards [he, Erdos821.S56Core.tendsto_L.eventually (eventually_ge_atTop 0)]
    with x hx hL
  intro G hG
  apply summable_and_tsum_le_of_Icc _ _ (groupHarmonicTerm_nonneg P G)
    (by simp [groupHarmonicTerm])
  intro N
  exact (harmonic_sum_le_tilted P G x hL N).trans (hx G hG N)

theorem harmonicP_summable_polylog (D : BandData) (hD : D.Valid) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      Summable (groupHarmonicTerm D.geometry (D.groups x)) ∧
        D.harmonicP x ≤ L x ^ C := by
  obtain ⟨C, he⟩ := group_harmonic_summable_polylog D.geometry
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, hv⟩ := hD
  refine ⟨C, ?_⟩
  filter_upwards [he, hv] with x hx hvx
  exact hx (D.groups x) hvx.1

/-- The finite Rankin tail estimate passes to the infinite harmonic measure. -/
theorem group_harmonic_tail (P : Geometry) (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ G : PrimeGroups, Admissible P x G →
      (∑' r : ℕ, if x ^ sigma < (r : ℝ) then groupHarmonicTerm P G r else 0) ≤
        Real.exp (-sigma * L x ^ (1 - P.d)) * L x ^ C := by
  have hm : Erdos821.S56Core.TiltedGroupMassTask :=
    Erdos821.P6Mass.TiltedGroupMassTask_proof
  obtain ⟨C, he⟩ := Erdos821.S56Core.group_tail_of_tilted hm P sigma hsigma
  refine ⟨C, ?_⟩
  filter_upwards [he] with x hx
  intro G hG
  apply (summable_and_tsum_le_of_Icc
    (fun r => if x ^ sigma < (r : ℝ) then groupHarmonicTerm P G r else 0)
    _ (fun r => by split_ifs; exact groupHarmonicTerm_nonneg P G r; exact le_rfl)
    (by simp [groupHarmonicTerm]) ?_).2
  intro N
  have heq : (∑ r ∈ Finset.Icc 1 N,
      if x ^ sigma < (r : ℝ) then groupHarmonicTerm P G r else 0) =
      ∑ r ∈ Finset.Icc 1 N, if groupFreePart G r = 1 ∧ x ^ sigma < (r : ℝ) then
        markWeight G P.q (fun _ => P.ell) r / r else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr0 : 0 < r := (Finset.mem_Icc.mp hr).1
    by_cases hp : groupFreePart G r = 1 <;> by_cases hc : x ^ sigma < (r : ℝ) <;>
      simp [groupHarmonicTerm, hr0, hp, hc]
  rw [heq]
  exact hx G hG N

theorem harmonicP_tail (D : BandData) (hD : D.Valid) (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      (∑' r : ℕ, if x ^ sigma < (r : ℝ) then
        groupHarmonicTerm D.geometry (D.groups x) r else 0) ≤
          Real.exp (-sigma * L x ^ (1 - D.geometry.d)) * L x ^ C := by
  obtain ⟨C, he⟩ := group_harmonic_tail D.geometry sigma hsigma
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, hv⟩ := hD
  refine ⟨C, ?_⟩
  filter_upwards [he, hv] with x hx hvx
  exact hx (D.groups x) hvx.1

end Erdos821.P7Core

