import Erdos821.P7.HarmonicP
import Erdos821.S56.GroupParts

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

abbrev SingleGroupChoice (G : PrimeGroups) := (g : Fin G.size) → Label G g

def singleGroupProduct {G : PrimeGroups} (z : SingleGroupChoice G) : ℕ :=
  ∏ g, (z g).val

theorem singleGroupProduct_pos {G : PrimeGroups} (z : SingleGroupChoice G) :
    0 < singleGroupProduct z := by
  exact Finset.prod_pos (fun g _ => (G.prime g _ (z g).property).pos)

/-- A prime from a specified group can divide the product only at that
group's own coordinate. -/
theorem singleGroupProduct_dvd_iff {G : PrimeGroups} (z : SingleGroupChoice G)
    (g : Fin G.size) (p : ℕ) (hp : p ∈ G.primes g) :
    p ∣ singleGroupProduct z ↔ p = (z g).val := by
  constructor
  · intro hdvd
    obtain ⟨h, _, hdiv⟩ := ((G.prime g p hp).prime.dvd_finsetProd_iff
      (fun h : Fin G.size => (z h).val)).mp hdvd
    have heq := (Nat.prime_dvd_prime_iff_eq (G.prime g p hp)
      (G.prime h _ (z h).property)).mp hdiv
    have hph : p ∈ G.primes h := heq.symm ▸ (z h).property
    have hh : h = g := by
      by_contra hne
      exact Finset.disjoint_left.mp (G.disjoint g h (Ne.symm hne)) hp hph
    subst h
    exact heq
  · intro heq
    rw [heq]
    exact Finset.dvd_prod_of_mem (fun h : Fin G.size => (z h).val) (Finset.mem_univ g)

theorem singleGroupProduct_injective (G : PrimeGroups) :
    Function.Injective (singleGroupProduct (G := G)) := by
  intro z w heq
  funext g
  apply Subtype.ext
  have hdiv : (z g).val ∣ singleGroupProduct w := by
    rw [← heq]
    exact (singleGroupProduct_dvd_iff z g _ (z g).property).2 rfl
  exact (singleGroupProduct_dvd_iff w g _ (z g).property).1 hdiv

theorem singleGroupProduct_omegaGroup {G : PrimeGroups} (z : SingleGroupChoice G)
    (g : Fin G.size) : omegaGroup G g (singleGroupProduct z) = 1 := by
  have heq : (G.primes g).filter (fun p => p ∣ singleGroupProduct z) = {(z g).val} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hdiv⟩
      exact (singleGroupProduct_dvd_iff z g p hp).1 hdiv
    · intro hp
      subst p
      exact ⟨(z g).property, (singleGroupProduct_dvd_iff z g _ (z g).property).2 rfl⟩
  simp only [omegaGroup, heq, Finset.card_singleton]

theorem singleGroupProduct_omega {G : PrimeGroups} (z : SingleGroupChoice G) :
    omega G (singleGroupProduct z) = G.size := by
  simp [omega, singleGroupProduct_omegaGroup]

theorem singleGroupProduct_pure {G : PrimeGroups} (z : SingleGroupChoice G) :
    groupFreePart G (singleGroupProduct z) = 1 := by
  have hsub : (singleGroupProduct z).primeFactors ⊆ Finset.univ.biUnion G.primes := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hdiv := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨g, _, hpg⟩ := (hpprime.prime.dvd_finsetProd_iff
      (fun g : Fin G.size => (z g).val)).mp hdiv
    have heq := (Nat.prime_dvd_prime_iff_eq hpprime (G.prime g _ (z g).property)).mp hpg
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, heq.symm ▸ (z g).property⟩
  simp [groupFreePart, Finset.sdiff_eq_empty_iff_subset.mpr hsub]

theorem singleGroupProduct_markWeight {G : PrimeGroups} (z : SingleGroupChoice G)
    (q : ℝ) :
    markWeight G q (fun _ => 1) (singleGroupProduct z) = ∏ g, (mass G g)⁻¹ := by
  simp [markWeight, singleGroupProduct_omega, singleGroupProduct_omegaGroup]

theorem singleGroupProduct_harmonicTerm {G : PrimeGroups} (z : SingleGroupChoice G)
    (P : Geometry) (hell : P.ell = 1) :
    groupHarmonicTerm P G (singleGroupProduct z) =
      ∏ g, (mass G g)⁻¹ * ((z g).val : ℝ)⁻¹ := by
  simp only [groupHarmonicTerm, singleGroupProduct_pos, singleGroupProduct_pure,
    and_self, ite_true, hell, singleGroupProduct_markWeight]
  simp only [singleGroupProduct, Nat.cast_prod, div_eq_mul_inv, Finset.prod_inv_distrib,
    Finset.prod_mul_distrib]

/-- The squarefree family with one prime from each group has normalized
marked harmonic mass exactly one. -/
theorem singleGroupChoice_harmonic_sum (P : Geometry) (G : PrimeGroups)
    (hell : P.ell = 1) (hmass : ∀ g, 0 < mass G g) :
    (∑ z : SingleGroupChoice G, groupHarmonicTerm P G (singleGroupProduct z)) = 1 := by
  simp_rw [singleGroupProduct_harmonicTerm _ P hell]
  rw [← Fintype.prod_sum (fun g (p : Label G g) => (mass G g)⁻¹ * (p.val : ℝ)⁻¹)]
  have hgroup (g : Fin G.size) :
      (∑ p : Label G g, (mass G g)⁻¹ * (p.val : ℝ)⁻¹) = 1 := by
    rw [← Finset.mul_sum]
    have heq : (∑ p : Label G g, (p.val : ℝ)⁻¹) = mass G g := by
      simpa only [mass, one_div] using
        Finset.sum_coe_sort (G.primes g) (fun p : ℕ => (p : ℝ)⁻¹)
    rw [heq, inv_mul_cancel₀ (hmass g).ne']
  simp only [hgroup, Finset.prod_const_one]

theorem group_harmonic_ge_one (P : Geometry) (G : PrimeGroups) (hell : P.ell = 1)
    (hmass : ∀ g, 0 < mass G g) (hsum : Summable (groupHarmonicTerm P G)) :
    1 ≤ ∑' r, groupHarmonicTerm P G r := by
  let s : Finset ℕ := Finset.univ.image (singleGroupProduct (G := G))
  have hsumone : (∑ r ∈ s, groupHarmonicTerm P G r) = 1 := by
    rw [Finset.sum_image (singleGroupProduct_injective G).injOn]
    exact singleGroupChoice_harmonic_sum P G hell hmass
  rw [← hsumone]
  exact hsum.sum_le_tsum s (fun r _ => groupHarmonicTerm_nonneg P G r)

theorem harmonicP_ge_one (D : BandData) (hD : D.Valid) (hell : D.geometry.ell = 1) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ D.harmonicP x := by
  obtain ⟨C, hs⟩ := harmonicP_summable_polylog D hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, hv⟩ := hD
  filter_upwards [hs, hv] with x hx hvx
  have hmass (g : Fin (D.groups x).size) : 0 < mass (D.groups x) g :=
    D.geometry.positive.2.2.1.trans_le (hvx.1.2.2.1 g).1
  exact group_harmonic_ge_one D.geometry (D.groups x) hell hmass hx.1

theorem geometry_harmonicP_ge_one (C : CandidateData) (δ : ℝ) (hC : C.Geometry δ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ C.bands.harmonicP x := by
  rcases hC with ⟨hD, _, _, _, _, _, _, _, _, _, hell, _⟩
  exact harmonicP_ge_one C.bands hD hell

end Erdos821.P7Core

