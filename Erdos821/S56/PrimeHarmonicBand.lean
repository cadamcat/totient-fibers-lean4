import Erdos821.Blueprint.Classical

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint

def reciprocalMass (s : Finset ℕ) : ℝ := ∑ p ∈ s, (p : ℝ)⁻¹

/-- Mertens on two prefixes bounds every finite prime interval; using lo/2
keeps the inclusive lower endpoint out of the lower prefix. -/
theorem prime_harmonic_interval (K lo hi : ℝ)
    (hM : ∀ y : ℝ, 2 ≤ y → |reciprocalMass (primesUpTo y) - Real.log (Real.log y)| ≤ K)
    (hlo : 4 ≤ lo) (hhi : lo ≤ hi) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi) :
    reciprocalMass s ≤ Real.log (Real.log hi) - Real.log (Real.log (lo / 2)) + 2 * K := by
  have hlo0 : 0 < lo := by linarith
  have hmid0 : 0 ≤ lo / 2 := by linarith
  have hhi0 : 0 ≤ hi := by linarith
  have hprefix : primesUpTo (lo / 2) ⊆ primesUpTo hi := by
    intro p hp
    obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hph⟩ := Finset.mem_Icc.mp hpI
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hp1, hph.trans (Nat.floor_mono (by linarith : lo / 2 ≤ hi))⟩, hprime⟩
  have hsubset : s ⊆ primesUpTo hi := by
    intro p hp
    obtain ⟨hprime, hpl, hph⟩ := hs p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.succ_le_of_lt hprime.pos, Nat.le_floor hph⟩, hprime⟩
  have hdisjoint : Disjoint (primesUpTo (lo / 2)) s := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hmid := (Nat.le_floor_iff hmid0).mp (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hpl := (hs p hp').2.1
    linarith
  have hunion : reciprocalMass (primesUpTo (lo / 2)) + reciprocalMass s ≤
      reciprocalMass (primesUpTo hi) := by
    unfold reciprocalMass
    rw [← Finset.sum_union hdisjoint]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hprefix hsubset)
      (fun p _ _ => by positivity)
  have hlower := (abs_le.mp (hM (lo / 2) (by linarith))).1
  have hupper := (abs_le.mp (hM hi (by linarith))).2
  linarith

theorem prime_harmonic_band (K c1 c2 sscale : ℝ)
    (hM : ∀ y : ℝ, 2 ≤ y → |reciprocalMass (primesUpTo y) - Real.log (Real.log y)| ≤ K)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hs : 0 < sscale) (hlarge : Real.log 4 ≤ c1 * sscale)
    (s : Finset ℕ)
    (hpr : ∀ p ∈ s, p.Prime ∧ Real.exp (c1 * sscale) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (c2 * sscale)) :
    reciprocalMass s ≤ Real.log (2 * c2 / c1) + 2 * K := by
  have hc2 : 0 < c2 := hc1.trans hc12
  have hlo : 4 ≤ Real.exp (c1 * sscale) := by
    have h := Real.exp_le_exp.mpr hlarge
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4)] using h
  have hhi := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc12.le hs.le)
  have hraw := prime_harmonic_interval K _ _ hM hlo hhi s hpr
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hlogmid : Real.log (Real.exp (c1 * sscale) / 2) = c1 * sscale - Real.log 2 := by
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp]
  have hmid : 0 < c1 * sscale / 2 := by positivity
  have hcompare : c1 * sscale / 2 ≤ c1 * sscale - Real.log 2 := by rw [hlog4] at hlarge; linarith
  have hlogcompare := Real.log_le_log hmid hcompare
  have hratio : c2 * sscale / (c1 * sscale / 2) = 2 * c2 / c1 := by
    field_simp [hc1.ne', hs.ne']
  have hlogratio : Real.log (c2 * sscale) - Real.log (c1 * sscale / 2) =
      Real.log (2 * c2 / c1) := by
    rw [← Real.log_div (mul_pos hc2 hs).ne' hmid.ne', hratio]
  rw [Real.log_exp, hlogmid] at hraw
  linarith


end Erdos821.S56Core
