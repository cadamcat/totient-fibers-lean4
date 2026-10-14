import Erdos821.P7.Positivity
import Erdos821.S56.HarmonicQ
import Erdos821.S56.GroupComponents
import Erdos821.S56.RoughFree

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Reindex the literal fibers without discarding repeated labelled lists. -/
theorem aQ_test_sum (D : BandData) (x : ℝ) (jstar : ℕ)
    (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ v ∈ s, D.aQ x jstar v * f v) =
      ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ *
        ∑ z : D.Lists x jstar, if D.listProduct z ∈ s then f (D.listProduct z) else 0 := by
  have hf (v : ℕ) :
      ((Finset.univ.filter (fun z : D.Lists x jstar => D.listProduct z = v)).card : ℝ) * f v =
        ∑ z : D.Lists x jstar, if D.listProduct z = v then f v else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [BandData.aQ, mul_assoc, hf, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simpa only [eq_comm] using Finset.sum_ite_eq' s (D.listProduct z) f

/-- The coefficient harmonic sum on its complete finite support is exactly HQ. -/
theorem harmonicQ_eq_image_sum (D : BandData) (x : ℝ) (jstar : ℕ) :
    (∑ v ∈ Finset.univ.image (fun z : D.Lists x jstar => D.listProduct z),
      D.aQ x jstar v / v) = D.harmonicQ x jstar := by
  simp only [div_eq_mul_inv]
  rw [aQ_test_sum]
  have hm (z : D.Lists x jstar) :
      D.listProduct z ∈ Finset.univ.image (fun z : D.Lists x jstar => D.listProduct z) :=
    Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
  simp only [hm, ite_true]
  rw [Erdos821.S56Core.tuple_harmonic_factorization]
  rfl

theorem listProduct_pos (D : BandData) {x : ℝ} {jstar : ℕ} (z : D.Lists x jstar) :
    0 < D.listProduct z := by
  exact Finset.prod_pos (fun s _ => Erdos821.S56Core.slot_value_pos D z s)

/-- Disjoint pure bands and the roughness threshold make the full Q-list
group-free, including the exceptional slot. -/
theorem listProduct_groupFree (D : BandData) (x : ℝ) (jstar : ℕ)
    (hdisjoint : ∀ j ≤ D.last x, ∀ g,
      Disjoint (D.band x j) ((D.groups x).primes g))
    (hrough : ∀ n, rough (W x) n → Erdos821.S56Core.GroupFree (D.groups x) n)
    (z : D.Lists x jstar) : Erdos821.S56Core.GroupFree (D.groups x) (D.listProduct z) := by
  apply Erdos821.S56Core.groupFree_prod
  intro s _
  have hz := (z s).property
  change (z s).val ∈ D.slotValues x jstar s at hz
  by_cases he : s.1.val = jstar ∧ s.2.val = 0
  · simp only [BandData.slotValues, if_pos he] at hz
    exact hrough _ (Finset.mem_filter.mp hz).2
  · simp only [BandData.slotValues, if_neg he] at hz
    have hzprime := (Finset.mem_filter.mp hz).2
    intro p hp hdvd
    obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
    have heq := (Nat.prime_dvd_prime_iff_eq ((D.groups x).prime g p hpg) hzprime).mp hdvd
    subst p
    exact Finset.disjoint_left.mp (hdisjoint s.1.val (by omega) g) hz hpg

theorem eventually_listProduct_groupFree (D : BandData) (hD : D.Valid) :
    ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ, ∀ z : D.Lists x jstar,
      Erdos821.S56Core.GroupFree (D.groups x) (D.listProduct z) := by
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, he⟩ := hD
  filter_upwards [he, Erdos821.S56Core.eventually_rough_groupFree D.geometry] with x hx hr
  intro jstar z
  exact listProduct_groupFree D x jstar hx.2.2.2.2 (hr (D.groups x) hx.1) z

/-- A fixed group-free factor gives a bijection between its fiber and the
positive pure group parts. The interval bound stays on the full product. -/
theorem group_fiber_sum (G : PrimeGroups) (q : ℝ) (t : Fin G.size → ℕ)
    (v N : ℕ) (hv : 0 < v) (hfree : Erdos821.S56Core.GroupFree G v) (f : ℕ → ℝ) :
    (∑ u ∈ Finset.Icc 1 N,
      if groupFreePart G u = v then markWeight G q t u * f u else 0) =
    ∑ r ∈ Finset.Icc 1 N,
      if groupFreePart G r = 1 ∧ v * r ≤ N then markWeight G q t r * f (v * r) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => Erdos821.S56Core.groupPart G u)
  · intro u hu
    obtain ⟨huI, hufree⟩ := Finset.mem_filter.mp hu
    have hu0 := (Finset.mem_Icc.mp huI).1
    obtain ⟨hprod, hpure, _⟩ := Erdos821.S56Core.group_components G u hu0 q t
    rw [hufree] at hprod
    have hrN := (Nat.le_of_dvd hu0 (Erdos821.S56Core.groupPart_dvd G u hu0)).trans
      (Finset.mem_Icc.mp huI).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Erdos821.S56Core.groupPart_pos G u, hrN⟩, hpure,
      hprod.le.trans (Finset.mem_Icc.mp huI).2⟩
  · intro u hu w hw heq
    obtain ⟨huI, hufree⟩ := Finset.mem_filter.mp hu
    obtain ⟨hwI, hwfree⟩ := Finset.mem_filter.mp hw
    have hpu := (Erdos821.S56Core.group_components G u (Finset.mem_Icc.mp huI).1 q t).1
    have hpw := (Erdos821.S56Core.group_components G w (Finset.mem_Icc.mp hwI).1 q t).1
    rw [hufree] at hpu
    rw [hwfree, ← heq] at hpw
    exact hpu.symm.trans hpw
  · intro r hr
    obtain ⟨hrI, hpure, hN⟩ := Finset.mem_filter.mp hr
    have hr0 := (Finset.mem_Icc.mp hrI).1
    have hproduct : groupFreePart G (v * r) = v := by
      rw [Erdos821.S56Core.groupFreePart_mul G v r hv hr0 hfree, hpure, mul_one]
    refine ⟨v * r, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨mul_pos hv hr0, hN⟩, hproduct⟩, ?_⟩
    have hp := (Erdos821.S56Core.group_components G (v * r) (mul_pos hv hr0) q t).1
    rw [hproduct] at hp
    exact Nat.eq_of_mul_eq_mul_left hv hp
  · intro u hu
    obtain ⟨huI, hufree⟩ := Finset.mem_filter.mp hu
    obtain ⟨hprod, _, hweight⟩ := Erdos821.S56Core.group_components G u
      (Finset.mem_Icc.mp huI).1 q t
    rw [hufree] at hprod
    rw [hprod, hweight]

/-- Exact finite product expression for the candidate mass. This is the
unnormalized form of the paper's independent harmonic choices. -/
theorem candidate_mass_product (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (hfree : ∀ z : C.bands.Lists x jstar,
      Erdos821.S56Core.GroupFree (C.bands.groups x) (C.bands.listProduct z)) :
    C.mass x jstar =
      ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        ∑ z : C.bands.Lists x jstar, ∑ r ∈ Finset.Icc 1 ⌊2 * x⌋₊,
          if groupFreePart (C.bands.groups x) r = 1 ∧
              C.bands.listProduct z * r ≤ ⌊2 * x⌋₊ then
            markWeight (C.bands.groups x) C.bands.geometry.q
              (fun _ => C.bands.geometry.ell) r *
                C.psi ((C.bands.listProduct z * r : ℕ) / x)
          else 0 := by
  have hf (v : ℕ) (a : ℝ) : C.bands.aQ x jstar v * a =
      ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        ∑ z : C.bands.Lists x jstar,
          if C.bands.listProduct z = v then a else 0 := by
    rw [BandData.aQ, mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
  unfold CandidateData.mass CandidateData.weighted BandData.weight
  simp only [mul_assoc]
  simp only [hf, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [eq_comm (a := C.bands.listProduct z)]
  exact group_fiber_sum (C.bands.groups x) C.bands.geometry.q
    (fun _ => C.bands.geometry.ell) (C.bands.listProduct z) ⌊2 * x⌋₊
    (listProduct_pos C.bands z) (hfree z) (fun u => C.psi ((u : ℝ) / x))

theorem eventually_candidate_mass_product (C : CandidateData) (δ : ℝ) (hC : C.Geometry δ) :
    ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ,
      C.mass x jstar =
        ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
          ∑ z : C.bands.Lists x jstar, ∑ r ∈ Finset.Icc 1 ⌊2 * x⌋₊,
            if groupFreePart (C.bands.groups x) r = 1 ∧
                C.bands.listProduct z * r ≤ ⌊2 * x⌋₊ then
              markWeight (C.bands.groups x) C.bands.geometry.q
                (fun _ => C.bands.geometry.ell) r *
                  C.psi ((C.bands.listProduct z * r : ℕ) / x)
            else 0 := by
  filter_upwards [eventually_listProduct_groupFree C.bands hC.1] with x hx
  exact fun jstar => candidate_mass_product C x jstar (hx jstar)

end Erdos821.P7Core

