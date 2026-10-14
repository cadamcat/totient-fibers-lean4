import Erdos821.S56.GroupComponents
import Erdos821.S56.HarmonicQ
import Erdos821.S56.WeightBound

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The positive group/free decomposition is an injective finite change of
variables. Multiplying harmonic mass by N bounds ordinary mass up to N. -/
theorem finite_group_tail_bound (G : PrimeGroups) (q : ℝ) (hq : 0 ≤ q)
    (t : Fin G.size → ℕ) (w : ℕ → ℝ) (hw : ∀ v, 0 ≤ w v)
    (N : ℕ) (Y : ℝ) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 N)
    (hbad : ∀ u ∈ s, Y < (groupPart G u : ℝ)) :
    (∑ u ∈ s, w (groupFreePart G u) * markWeight G q t u) ≤
      (N : ℝ) * (∑ v ∈ Finset.Icc 1 N, w v / v) *
        ∑ r ∈ Finset.Icc 1 N,
          if groupFreePart G r = 1 ∧ Y < (r : ℝ) then markWeight G q t r / r else 0 := by
  let f : ℕ → ℕ × ℕ := fun u => (groupFreePart G u, groupPart G u)
  let R := (Finset.Icc 1 N).filter (fun r => groupFreePart G r = 1 ∧ Y < (r : ℝ))
  let A : ℕ × ℕ → ℝ := fun p => (w p.1 / p.1) * (markWeight G q t p.2 / p.2)
  have hpos (u : ℕ) (hu : u ∈ s) : 0 < u := (Finset.mem_Icc.mp (hs hu)).1
  have hsub : s.image f ⊆ (Finset.Icc 1 N) ×ˢ R := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    have hu0 := hpos u hu
    obtain ⟨hprod, hpure, hweight⟩ := group_components G u hu0 q t
    have hulo := (Finset.mem_Icc.mp (hs hu)).2
    have hvN := (Nat.le_of_dvd hu0 (groupFreePart_dvd G u hu0)).trans hulo
    have hrN := (Nat.le_of_dvd hu0 (groupPart_dvd G u hu0)).trans hulo
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨groupFreePart_pos G u, hvN⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨groupPart_pos G u, hrN⟩, hpure, hbad u hu⟩⟩
  have hinj : Set.InjOn f s := by
    intro u hu v hv heq
    have he1 := congrArg Prod.fst heq
    have he2 := congrArg Prod.snd heq
    change groupFreePart G u = groupFreePart G v at he1
    change groupPart G u = groupPart G v at he2
    have hu' := (group_components G u (hpos u hu) q t).1
    have hv' := (group_components G v (hpos v hv) q t).1
    calc
      u = groupFreePart G u * groupPart G u := hu'.symm
      _ = groupFreePart G v * groupPart G v := by rw [he1, he2]
      _ = v := hv'
  have hA (p : ℕ × ℕ) : 0 ≤ A p :=
    mul_nonneg (div_nonneg (hw _) (Nat.cast_nonneg _))
      (div_nonneg (markWeight_nonneg G q hq t _) (Nat.cast_nonneg _))
  have hpoint (u : ℕ) (hu : u ∈ s) :
      w (groupFreePart G u) * markWeight G q t u ≤ (N : ℝ) * A (f u) := by
    obtain ⟨hprod, hpure, hweight⟩ := group_components G u (hpos u hu) q t
    have hv : (0 : ℝ) < groupFreePart G u := by exact_mod_cast groupFreePart_pos G u
    have hr : (0 : ℝ) < groupPart G u := by exact_mod_cast groupPart_pos G u
    have hprodR : (u : ℝ) = (groupFreePart G u : ℝ) * (groupPart G u : ℝ) := by
      exact_mod_cast hprod.symm
    have heq : w (groupFreePart G u) * markWeight G q t u = (u : ℝ) * A (f u) := by
      rw [hweight, hprodR]
      dsimp [A, f]
      field_simp [hv.ne', hr.ne']
    rw [heq]
    apply mul_le_mul_of_nonneg_right _ (hA _)
    exact_mod_cast (Finset.mem_Icc.mp (hs hu)).2
  calc
    _ ≤ ∑ u ∈ s, (N : ℝ) * A (f u) := Finset.sum_le_sum (fun u hu => hpoint u hu)
    _ = (N : ℝ) * ∑ u ∈ s, A (f u) := (Finset.mul_sum _ _ _).symm
    _ = (N : ℝ) * ∑ p ∈ s.image f, A p := by rw [Finset.sum_image hinj]
    _ ≤ (N : ℝ) * ∑ p ∈ (Finset.Icc 1 N) ×ˢ R, A p :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hA p))
        (Nat.cast_nonneg N)
    _ = (N : ℝ) * (∑ v ∈ Finset.Icc 1 N, w v / v) *
        ∑ r ∈ R, markWeight G q t r / r := by
      simp only [A, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
    _ = _ := by rw [Finset.sum_filter]

theorem band_group_tail_bound (D : BandData) (x : ℝ) (jstar N : ℕ) (Y : ℝ) :
    (∑ u ∈ Finset.Icc 1 N,
      if Y < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0) ≤
      (N : ℝ) * D.harmonicQ x jstar *
        ∑ r ∈ Finset.Icc 1 N,
          if groupFreePart (D.groups x) r = 1 ∧ Y < (r : ℝ) then
            markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) r / r else 0 := by
  let s := (Finset.Icc 1 N).filter (fun u => Y < (groupPart (D.groups x) u : ℝ))
  have h := finite_group_tail_bound (D.groups x) D.geometry.q D.geometry.damping.1.le
    (fun _ => D.geometry.ell) (D.aQ x jstar) (aQ_nonneg D x jstar) N Y s
    (Finset.filter_subset _ _) (fun u hu => (Finset.mem_filter.mp hu).2)
  rw [← Finset.sum_filter]
  refine h.trans ?_
  have htail0 : 0 ≤ ∑ r ∈ Finset.Icc 1 N,
      if groupFreePart (D.groups x) r = 1 ∧ Y < (r : ℝ) then
        markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) r / r else 0 := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact div_nonneg (markWeight_nonneg _ _ D.geometry.damping.1.le _ _) (Nat.cast_nonneg r)
    · exact le_rfl
  apply mul_le_mul_of_nonneg_right _ htail0
  exact mul_le_mul_of_nonneg_left (harmonic_aQ_le D x jstar N) (Nat.cast_nonneg N)


end Erdos821.S56Core
