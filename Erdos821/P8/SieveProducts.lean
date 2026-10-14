import Erdos821.Blueprint.Proxy
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Order.Filter.AtTopBot.Finset

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint

def eulerDeficit (p : {p : ℕ // p.Prime}) : ℝ :=
  if p.val = 2 then 0 else (((p.val : ℝ) - 1)⁻¹) ^ 2

def eulerFactor (p : {p : ℕ // p.Prime}) : ℝ := 1 - eulerDeficit p

def primeCutoff (y : ℝ) : Finset {p : ℕ // p.Prime} :=
  (primesUpTo y).subtype Nat.Prime

lemma eulerDeficit_nonneg (p : {p : ℕ // p.Prime}) : 0 ≤ eulerDeficit p := by
  unfold eulerDeficit
  split_ifs <;> positivity

lemma eulerFactor_pos (p : {p : ℕ // p.Prime}) : 0 < eulerFactor p := by
  unfold eulerFactor eulerDeficit
  split_ifs with hp
  · norm_num
  · have hp3 : 3 ≤ p.val := by have := p.property.two_le; omega
    have hp3r : (3 : ℝ) ≤ p.val := by exact_mod_cast hp3
    have hp1 : 1 < (p.val : ℝ) - 1 := by linarith
    have hi0 : 0 < ((p.val : ℝ) - 1)⁻¹ := inv_pos.mpr (by linarith)
    have hi1 : ((p.val : ℝ) - 1)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hp1
    nlinarith

lemma summable_eulerDeficit : Summable eulerDeficit := by
  have hinj : Function.Injective (fun p : {p : ℕ // p.Prime} => p.val - 1) := by
    intro p q hpq
    apply Subtype.ext
    change p.val - 1 = q.val - 1 at hpq
    have := p.property.two_le
    have := q.property.two_le
    omega
  have hs : Summable (fun p : {p : ℕ // p.Prime} => (((p.val - 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (show 1 < (2 : ℕ) by decide)).comp_injective hinj
  have heq (p : {p : ℕ // p.Prime}) : (((p.val - 1 : ℕ) : ℝ) ^ 2)⁻¹ =
      (((p.val : ℝ) - 1)⁻¹) ^ 2 := by
    rw [Nat.cast_sub (by have := p.property.two_le; omega), Nat.cast_one, inv_pow]
  refine Summable.of_nonneg_of_le eulerDeficit_nonneg ?_ hs
  · intro p
    rw [heq]
    unfold eulerDeficit
    split_ifs
    · positivity
    · exact le_rfl

lemma summable_log_eulerFactor : Summable (fun p => Real.log (eulerFactor p)) := by
  simpa [eulerFactor, sub_eq_add_neg] using
    Real.summable_log_one_add_of_summable summable_eulerDeficit.neg

lemma hasProd_eulerFactor :
    HasProd eulerFactor (Real.exp (∑' p, Real.log (eulerFactor p))) :=
  Real.hasProd_of_hasSum_log eulerFactor_pos summable_log_eulerFactor.hasSum

lemma singularSeries_eq_exp :
    singularSeries = 2 * Real.exp (∑' p, Real.log (eulerFactor p)) := by
  unfold singularSeries
  change 2 * (∏' p : {p : ℕ // p.Prime}, if p.val = 2 then 1 else
    1 - (((p.val : ℝ) - 1)⁻¹) ^ 2) = _
  have heq : (fun p : {p : ℕ // p.Prime} => if p.val = 2 then (1 : ℝ) else
      1 - (((p.val : ℝ) - 1)⁻¹) ^ 2) = eulerFactor := by
    funext p
    unfold eulerFactor eulerDeficit
    split_ifs <;> simp
  rw [heq, hasProd_eulerFactor.tprod_eq]

lemma singularSeries_pos : 0 < singularSeries := by
  rw [singularSeries_eq_exp]
  positivity

lemma mem_primesUpTo {p : ℕ} {y : ℝ} :
    p ∈ primesUpTo y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  unfold primesUpTo
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp1, hpy⟩, hp⟩
    exact ⟨hp, (Nat.le_floor_iff' hp.ne_zero).mp hpy⟩
  · rintro ⟨hp, hpy⟩
    exact ⟨⟨by have := hp.two_le; omega, (Nat.le_floor_iff' hp.ne_zero).mpr hpy⟩, hp⟩

lemma primeCutoff_tendsto : Tendsto primeCutoff atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro a b hab p hp
    rw [primeCutoff, Finset.mem_subtype, mem_primesUpTo] at hp ⊢
    exact ⟨hp.1, hp.2.trans hab⟩
  · intro p
    exact ⟨(p.val : ℝ), by simp [primeCutoff, Finset.mem_subtype, mem_primesUpTo, p.property]⟩

lemma finite_factor_ratio {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (1 - ((p : ℝ) - 1)⁻¹) / (1 - (p : ℝ)⁻¹) =
      1 - (((p : ℝ) - 1)⁻¹) ^ 2 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hd : 1 - (p : ℝ)⁻¹ ≠ 0 := by
    have hlt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr
      (by linarith)
    linarith
  field_simp
  <;> ring

lemma sieveProduct_pos (y : ℝ) : 0 < sieveProduct y := by
  apply Finset.prod_pos
  intro p hp
  have hp2 := (mem_primesUpTo.mp hp).1.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hlt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  linarith

lemma sieveProduct_ratio (y : ℝ) (hy : 2 ≤ y) :
    shiftedSieveProduct y / sieveProduct y =
      2 * ∏ p ∈ primeCutoff y, eulerFactor p := by
  have htwo : 2 ∈ primesUpTo y := mem_primesUpTo.mpr ⟨Nat.prime_two, by exact_mod_cast hy⟩
  have hprod : sieveProduct y = (1 - (2 : ℝ)⁻¹) *
      ∏ p ∈ (primesUpTo y).erase 2, (1 - (p : ℝ)⁻¹) := by
    exact (Finset.mul_prod_erase (primesUpTo y) (fun p => 1 - (p : ℝ)⁻¹) htwo).symm
  have hn (p : ℕ) (hp : p ∈ (primesUpTo y).erase 2) : 1 - (p : ℝ)⁻¹ ≠ 0 := by
    have hp' := (mem_primesUpTo.mp (Finset.mem_of_mem_erase hp)).1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hp'.two_le; omega)
    have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
    linarith
  have hnonzero : (∏ p ∈ (primesUpTo y).erase 2, (1 - (p : ℝ)⁻¹)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hn
  have heq : (∏ p ∈ (primesUpTo y).erase 2,
      (1 - ((p : ℝ) - 1)⁻¹) / (1 - (p : ℝ)⁻¹)) =
      ∏ p ∈ primeCutoff y, eulerFactor p := by
    unfold primeCutoff
    rw [show eulerFactor = (fun p : {p : ℕ // p.Prime} =>
      if p.val = 2 then (1 : ℝ) else 1 - (((p.val : ℝ) - 1)⁻¹) ^ 2) by
        funext p; unfold eulerFactor eulerDeficit; split_ifs <;> simp]
    rw [Finset.prod_subtype_of_mem (fun p : ℕ =>
      if p = 2 then (1 : ℝ) else 1 - (((p : ℝ) - 1)⁻¹) ^ 2)
      (fun p hp => (mem_primesUpTo.mp hp).1)]
    rw [← Finset.prod_erase_mul (primesUpTo y) _ htwo]
    simp only [ite_true, mul_one]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
    simp only [hp2, ite_false]
    exact finite_factor_ratio (mem_primesUpTo.mp (Finset.mem_of_mem_erase hp)).1 hp2
  rw [shiftedSieveProduct, hprod, ← heq, Finset.prod_div_distrib]
  norm_num
  field_simp

theorem sieveProducts_proof : SieveProducts := by
  refine ⟨singularSeries_pos, ?_⟩
  have ht : Tendsto (fun y => ∏ p ∈ primeCutoff y, eulerFactor p) atTop
      (nhds (Real.exp (∑' p, Real.log (eulerFactor p)))) :=
    hasProd_eulerFactor.comp primeCutoff_tendsto
  rw [singularSeries_eq_exp]
  apply (tendsto_const_nhds.mul ht).congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
  exact (sieveProduct_ratio y hy).symm

example : SieveProducts := sieveProducts_proof

end Erdos821.P8Core

