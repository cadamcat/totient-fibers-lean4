import Erdos821.S9Mask.Harmonic

/-! The literal `harmonicP` sum factors over groups and dominates the full Euler product. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S9Mask
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- All group primes. -/
def gps (G : PrimeGroups) : Finset ℕ := Finset.univ.biUnion G.primes

theorem gps_prime (G : PrimeGroups) : ∀ p ∈ gps G, p.Prime := by
  intro p hp
  obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hp
  exact G.prime g p hg

theorem groupFreePart_eq_one_iff (G : PrimeGroups) (r : ℕ) (hr : 0 < r) :
    groupFreePart G r = 1 ↔ r.primeFactors ⊆ gps G := by
  unfold groupFreePart
  constructor
  · intro h p hp
    by_contra hnot
    have hmem : p ∈ r.primeFactors \ Finset.univ.biUnion G.primes :=
      Finset.mem_sdiff.mpr ⟨hp, hnot⟩
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hexp : 0 < r.factorization p :=
      hpprime.factorization_pos_of_dvd hr.ne' (Nat.dvd_of_mem_primeFactors hp)
    have hdvd : p ∣ ∏ p ∈ r.primeFactors \ Finset.univ.biUnion G.primes,
        p ^ r.factorization p :=
      dvd_trans (dvd_pow_self p (Nat.ne_of_gt hexp)) (Finset.dvd_prod_of_mem _ hmem)
    rw [h] at hdvd
    exact hpprime.one_lt.ne' (Nat.dvd_one.mp hdvd)
  · intro h
    rw [Finset.sdiff_eq_empty_iff_subset.mpr (show r.primeFactors ⊆ Finset.univ.biUnion G.primes from h),
      Finset.prod_empty]

theorem omega_eq_card_primeFactors (G : PrimeGroups) (r : ℕ) (hr : 0 < r)
    (hsub : r.primeFactors ⊆ gps G) : omega G r = r.primeFactors.card := by
  classical
  let family := fun g : Fin G.size => (G.primes g).filter fun p => p ∣ r
  have hdisj : (↑(Finset.univ : Finset (Fin G.size)) : Set (Fin G.size)).PairwiseDisjoint
      family := by
    intro g _ h _ hne
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    exact (Finset.disjoint_left.mp (G.disjoint g h hne))
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1
  have hunion : (Finset.univ : Finset (Fin G.size)).biUnion family = r.primeFactors := by
    ext p
    simp only [family, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨g, hg, hdiv⟩
      exact Nat.mem_primeFactors.mpr ⟨G.prime g p hg, hdiv, hr.ne'⟩
    · intro hp
      obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp (hsub hp)
      exact ⟨g, hg, Nat.dvd_of_mem_primeFactors hp⟩
  have hcard := Finset.card_biUnion hdisj
  rw [hunion] at hcard
  rw [hcard]
  rfl

theorem injective_of_mem_piFinset (G : PrimeGroups) (c : Fin G.size → ℕ)
    (hc : c ∈ Fintype.piFinset G.primes) : Function.Injective c := by
  intro g h heq
  by_contra hne
  have hg := Fintype.mem_piFinset.mp hc g
  have hh := Fintype.mem_piFinset.mp hc h
  rw [heq] at hg
  exact Finset.disjoint_left.mp (G.disjoint g h hne) hg hh

/-- Exact value of the literal multi-group harmonic sum with one mark per group. -/
theorem harmonic_mark_hasSum (G : PrimeGroups) (q : ℝ) (hq : 0 < q) :
    HasSum (fun r : ℕ => if 0 < r ∧ groupFreePart G r = 1 then
        markWeight G q (fun _ => 1) r / r else 0)
      ((∏ p ∈ gps G, (1 + q / ((p : ℝ) - 1))) *
        (∏ g, ∑ p ∈ G.primes g, q / ((p : ℝ) - 1 + q)) /
          (q ^ G.size * ∏ g, mass G g)) := by
  classical
  set E : ℝ := ∏ p ∈ gps G, (1 + q / ((p : ℝ) - 1)) with hE
  set K : ℝ := q ^ G.size * ∏ g, mass G g with hK
  let F : (Fin G.size → ℕ) → ℕ → ℝ := fun c r =>
    if 0 < r ∧ r.primeFactors ⊆ gps G ∧ (∀ p ∈ Finset.univ.image c, p ∣ r) then
      wHarm (fun _ => q) r else 0
  have hc : ∀ c ∈ Fintype.piFinset G.primes,
      HasSum (F c) (E * ∏ g, q / (((c g : ℕ) : ℝ) - 1 + q)) := by
    intro c hcmem
    have hA : Finset.univ.image c ⊆ gps G := by
      intro p hp
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, Fintype.mem_piFinset.mp hcmem g⟩
    have h := marked_hasSum (gps G) (Finset.univ.image c) (gps_prime G) hA q hq.le
    rw [Finset.prod_image (fun g _ h _ hgh => injective_of_mem_piFinset G c hcmem hgh)] at h
    convert h using 1
    funext n
    dsimp only [F]
    split_ifs <;> rfl
  have hsum := (hasSum_sum hc).div_const K
  rw [← Finset.mul_sum,
    ← Finset.prod_univ_sum (t := G.primes) (f := fun _ p => q / ((p : ℝ) - 1 + q))] at hsum
  refine hsum.congr_fun ?_
  intro r
  by_cases hr : r = 0
  · simp [F, hr]
  have hr0 : 0 < r := Nat.pos_of_ne_zero hr
  by_cases hsub : r.primeFactors ⊆ gps G
  · have hgf : groupFreePart G r = 1 := (groupFreePart_eq_one_iff G r hr0).mpr hsub
    rw [if_pos ⟨hr0, hgf⟩]
    have hF : ∀ c, F c r = wHarm (fun _ => q) r * ∏ g, (if c g ∣ r then (1 : ℝ) else 0) := by
      intro c
      simp only [F]
      by_cases hall : ∀ g, c g ∣ r
      · have : ∀ p ∈ Finset.univ.image c, p ∣ r := by
          intro p hp
          obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hp
          exact hall g
        rw [if_pos ⟨hr0, hsub, this⟩, Finset.prod_eq_one (fun g _ => if_pos (hall g)), mul_one]
      · push Not at hall
        obtain ⟨g, hg⟩ := hall
        have : ¬ ∀ p ∈ Finset.univ.image c, p ∣ r := fun h =>
          hg (h _ (Finset.mem_image_of_mem c (Finset.mem_univ g)))
        rw [if_neg (fun h => this h.2.2), Finset.prod_eq_zero (Finset.mem_univ g) (if_neg hg), mul_zero]
    simp only [hF]
    rw [← Finset.mul_sum, ← Finset.prod_univ_sum (t := G.primes)
      (f := fun _ p => if p ∣ r then (1 : ℝ) else 0)]
    have hω : ∀ g, (∑ p ∈ G.primes g, if p ∣ r then (1 : ℝ) else 0) =
        (omegaGroup G g r : ℝ) := by
      intro g
      rw [Finset.sum_boole]
      rfl
    simp only [hω]
    unfold markWeight
    rw [omega_eq_card_primeFactors G r hr0 hsub]
    simp only [Nat.descFactorial_one, pow_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [zpow_sub₀ hq.ne', zpow_natCast]
    simp only [wHarm, hr, ite_false, Finset.prod_const, div_eq_mul_inv,
      Finset.prod_mul_distrib, Finset.prod_inv_distrib, hK]
    simp only [Nat.cast_one, mul_one, zpow_natCast]
    ring
  · have hgf : groupFreePart G r ≠ 1 := fun h => hsub ((groupFreePart_eq_one_iff G r hr0).mp h)
    rw [if_neg (fun h => hgf h.2)]
    have hF : ∀ c, F c r = 0 := by
      intro c
      simp only [F]
      rw [if_neg (fun h => hsub h.2.1)]
    simp [hF]

end Erdos821.S9Mask

namespace Erdos821.S9Mask
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem euler_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ ∏ p ∈ P, (1 + q / ((p : ℝ) - 1)) := by
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
  exact add_nonneg zero_le_one (div_nonneg hq (by linarith))

/-- With positive group masses, the full group Euler product is at most `harmonicP`. -/
theorem euler_le_harmonicP (D : BandData) (x : ℝ) (hell : D.geometry.ell = 1)
    (hmass : ∀ g, 0 < mass (D.groups x) g) :
    (∏ p ∈ gps (D.groups x), (1 + D.geometry.q / ((p : ℝ) - 1))) ≤ D.harmonicP x := by
  set G := D.groups x with hG
  set q := D.geometry.q with hqdef
  have hq0 : 0 < q := D.geometry.damping.1
  have hq1 : q < 1 := D.geometry.damping.2
  have hsum := harmonic_mark_hasSum G q hq0
  have hP : D.harmonicP x = ∑' r : ℕ, if 0 < r ∧ groupFreePart G r = 1 then
      markWeight G q (fun _ => 1) r / r else 0 := by
    unfold BandData.harmonicP
    rw [hell]
  rw [hP, hsum.tsum_eq]
  set E := ∏ p ∈ gps G, (1 + q / ((p : ℝ) - 1))
  have hE : 0 ≤ E := euler_nonneg _ (gps_prime G) q hq0.le
  have hK : 0 < q ^ G.size * ∏ g, mass G g :=
    mul_pos (pow_pos hq0 _) (Finset.prod_pos fun g _ => hmass g)
  rw [le_div_iff₀ hK]
  apply mul_le_mul_of_nonneg_left _ hE
  have hKprod : q ^ G.size * ∏ g, mass G g = ∏ g, q * mass G g := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hKprod]
  calc
    (∏ g, q * mass G g) ≤ ∏ g, ∑ p ∈ G.primes g, q / ((p : ℝ) - 1 + q) := by
      apply Finset.prod_le_prod₀
      · intro g _
        exact (mul_pos hq0 (hmass g)).le
      · intro g _
        unfold mass
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (G.prime g p hp).one_lt
        rw [← div_eq_mul_one_div]
        exact div_le_div_of_nonneg_left hq0.le (by linarith) (by linarith)

end Erdos821.S9Mask
