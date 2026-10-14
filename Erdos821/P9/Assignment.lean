import Erdos821.Blueprint.Candidate
import Erdos821.P9.MaskEuler

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos821.Blueprint.Analytic

abbrev MarkOptions (G : PrimeGroups) (n : ℕ) (g : Fin G.size) :=
  {p : ℕ // p ∈ (G.primes g).filter (fun p => p ∣ n)}

abbrev MarkChoices (G : PrimeGroups) (n : ℕ) :=
  (g : Fin G.size) → MarkOptions G n g

def markChoiceCoefficient (G : PrimeGroups) (q : ℝ) (n : ℕ) : ℝ :=
  q ^ ((omega G n : ℤ) - G.size) * ∏ g, (mass G g)⁻¹

def markBaseCoefficient (G : PrimeGroups) (n : ℕ) : ℝ :=
  ∏ g, (mass G g)⁻¹

def listNormalizer (B : Erdos821.Blueprint.BandData) (x : ℝ) : ℝ :=
  ((B.r₀.factorial : ℝ) ^ (B.last x + 1))⁻¹

def microSlots (C : Erdos821.Blueprint.CandidateData) (x : ℝ) :
    Finset (C.bands.Slot x) :=
  Finset.univ.filter fun s => C.micro ≤ s.1.val

def macroSlots (C : Erdos821.Blueprint.CandidateData) (x : ℝ) :
    Finset (C.bands.Slot x) :=
  Finset.univ.filter fun s => s.1.val < C.micro

def microProduct (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ)
    (z : C.bands.Lists x jstar) : ℕ :=
  ∏ s ∈ microSlots C x, (z s).val

def macroProduct (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ)
    (z : C.bands.Lists x jstar) : ℕ :=
  ∏ s ∈ macroSlots C x, (z s).val

theorem micro_macro_slots_partition (C : Erdos821.Blueprint.CandidateData) (x : ℝ) :
    Disjoint (microSlots C x) (macroSlots C x) ∧
      microSlots C x ∪ macroSlots C x = Finset.univ := by
  classical
  constructor
  · refine Finset.disjoint_left.mpr ?_
    intro s hs hm
    simp only [microSlots, macroSlots, Finset.mem_filter, Finset.mem_univ, true_and] at hs hm
    omega
  · ext s
    simp [microSlots, macroSlots]
    omega

theorem microProduct_dvd_listProduct (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (z : C.bands.Lists x jstar) :
    microProduct C x jstar z ∣ C.bands.listProduct z := by
  classical
  unfold microProduct
  rw [Erdos821.Blueprint.BandData.listProduct]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

theorem listProduct_eq_micro_mul_macro (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (z : C.bands.Lists x jstar) :
    C.bands.listProduct z = microProduct C x jstar z * macroProduct C x jstar z := by
  classical
  have hpart := micro_macro_slots_partition C x
  rw [macroProduct, microProduct, ← Finset.prod_union hpart.1, hpart.2]
  rfl

theorem macro_slot_mem_band (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (z : C.bands.Lists x jstar)
    (s : C.bands.Slot x) (hs : s ∈ macroSlots C x)
    (hj : C.micro ≤ jstar) :
    (z s).val ∈ C.bands.band x s.1.val := by
  have hmacro : s.1.val < C.micro := (Finset.mem_filter.mp hs).2
  have hnot : ¬ (s.1.val = jstar ∧ s.2.val = 0) := by omega
  have hm := (z s).property
  simpa [Erdos821.Blueprint.BandData.slotValues, hnot] using hm

theorem macro_slot_prime_large (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (z : C.bands.Lists x jstar)
    (s : C.bands.Slot x) (hs : s ∈ macroSlots C x)
    (hj : C.micro ≤ jstar)
    (hscale : C.theta * Real.log x <
      C.bands.c₁ * C.bands.scale x s.1.val)
    (hx : 0 < x) :
    Nat.Prime (z s).val ∧ x ^ C.theta < (z s).val := by
  have hband := macro_slot_mem_band C x jstar z s hs hj
  have hprime := (Finset.mem_filter.mp hband).2
  have hinterval := (Finset.mem_filter.mp hband).1
  have hlo := (Finset.mem_Icc.mp hinterval).1
  have hexp_le : Real.exp (C.bands.c₁ * C.bands.scale x s.1.val) ≤ (z s).val := by
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hlo)
  have hpow : x ^ C.theta = Real.exp (C.theta * Real.log x) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  refine ⟨hprime, ?_⟩
  rw [hpow]
  exact (Real.exp_lt_exp.mpr hscale).trans_le hexp_le

theorem macro_scale_exceeds_theta (C : Erdos821.Blueprint.CandidateData)
    (δ x : ℝ) (hC : C.Geometry δ) (hx : 1 < x)
    (s : C.bands.Slot x) (hs : s ∈ macroSlots C x) :
    C.theta * Real.log x < C.bands.c₁ * C.bands.scale x s.1.val := by
  have hvalid := hC.1
  rcases hC with ⟨_, _, _, hratio, _, _, _, _, _, _, _, _, _, _, _, _, _, htheta, _, _, _, _, _⟩
  have hidx : s.1.val + 1 ≤ C.micro := by
    have hs' := (Finset.mem_filter.mp hs).2
    omega
  have hmicro : 0 < C.micro := by omega
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hidx' : s.1.val ≤ C.micro - 1 := by omega
  have hpowNat : (2 : ℕ) ^ s.1.val ≤ 2 ^ (C.micro - 1) :=
    Nat.pow_le_pow_right (by decide) hidx'
  have hpow : (2 : ℝ) ^ s.1.val ≤ (2 : ℝ) ^ (C.micro - 1) := by
    exact_mod_cast hpowNat
  have hinv : ((2 : ℝ) ^ (C.micro - 1))⁻¹ ≤ ((2 : ℝ) ^ s.1.val)⁻¹ := by
    apply (inv_le_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (C.micro - 1))
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ s.1.val)).2
    exact hpow
  have hscale : C.bands.c₁ * C.bands.scale x s.1.val =
      C.bands.c₁ * C.bands.s' * Real.log x / (2 : ℝ) ^ s.1.val := by
    simp [Erdos821.Blueprint.BandData.scale, hratio, Erdos821.Blueprint.Analytic.L]
    <;> ring
  have hpowEq : (2 : ℝ) ^ C.micro = (2 : ℝ) ^ (C.micro - 1) * 2 := by
    calc
      (2 : ℝ) ^ C.micro = (2 : ℝ) ^ (C.micro - 1 + 1) := by
        congr 1
        omega
      _ = (2 : ℝ) ^ (C.micro - 1) * 2 := by rw [pow_succ]
  have hbase : (2 * C.bands.c₁ * C.bands.s' / (2 : ℝ) ^ C.micro) * Real.log x ≤
      C.bands.c₁ * C.bands.s' * Real.log x / (2 : ℝ) ^ s.1.val := by
    rw [hpowEq]
    have hnum : 0 ≤ C.bands.c₁ * C.bands.s' * Real.log x :=
      mul_nonneg (mul_nonneg hvalid.2.1.le hvalid.2.2.2.1.le) hlog.le
    rw [div_eq_mul_inv]
    calc
      (2 * C.bands.c₁ * C.bands.s' / ((2 : ℝ) ^ (C.micro - 1) * 2)) * Real.log x =
          (C.bands.c₁ * C.bands.s' * Real.log x) * ((2 : ℝ) ^ (C.micro - 1))⁻¹ := by
            field_simp
            <;> ring
      _ ≤ (C.bands.c₁ * C.bands.s' * Real.log x) * ((2 : ℝ) ^ s.1.val)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hnum
      _ = C.bands.c₁ * C.bands.s' * Real.log x / (2 : ℝ) ^ s.1.val := by
        rw [div_eq_mul_inv]
  have hthetaL := mul_lt_mul_of_pos_right htheta hlog
  have hthetaL' : C.theta * Real.log x <
      (2 * C.bands.c₁ * C.bands.s' / (2 : ℝ) ^ C.micro) * Real.log x := by
    simpa [mul_assoc] using hthetaL
  calc
    C.theta * Real.log x <
        (2 * C.bands.c₁ * C.bands.s' / (2 : ℝ) ^ C.micro) * Real.log x := hthetaL'
    _ ≤ C.bands.c₁ * C.bands.s' * Real.log x / (2 : ℝ) ^ s.1.val := hbase
    _ = C.bands.c₁ * C.bands.scale x s.1.val := hscale.symm

theorem macro_slot_is_large (C : Erdos821.Blueprint.CandidateData)
    (δ x : ℝ) (hC : C.Geometry δ) (hx : 1 < x) (jstar : ℕ)
    (hj : C.micro ≤ jstar) (z : C.bands.Lists x jstar)
    (s : C.bands.Slot x) (hs : s ∈ macroSlots C x) :
    Nat.Prime (z s).val ∧ x ^ C.theta < (z s).val := by
  exact macro_slot_prime_large C x jstar z s hs hj
    (macro_scale_exceeds_theta C δ x hC hx s hs) (by linarith)

theorem macroProduct_has_no_small_prime (C : Erdos821.Blueprint.CandidateData)
    (δ x : ℝ) (hC : C.Geometry δ) (hx : 1 < x) (jstar : ℕ)
    (hj : C.micro ≤ jstar) (z : C.bands.Lists x jstar) (p : ℕ)
    (hp : p.Prime) (hsmall : (p : ℝ) ≤ x ^ C.theta) :
    ¬ p ∣ macroProduct C x jstar z := by
  intro hdiv
  obtain ⟨s, hs, hps⟩ := (hp.prime.dvd_finsetProd_iff (fun s => (z s).val)).mp hdiv
  have hlarge := macro_slot_is_large C δ x hC hx jstar hj z s hs
  have hEq : p = (z s).val := (Nat.prime_dvd_prime_iff_eq hp hlarge.1).mp hps
  have : x ^ C.theta < (p : ℝ) := by simpa [hEq] using hlarge.2
  exact (not_lt_of_ge hsmall) this

theorem small_groupFree_prime_divides_micro (C : Erdos821.Blueprint.CandidateData)
    (δ x : ℝ) (hC : C.Geometry δ) (hx : 1 < x) (jstar : ℕ)
    (hj : C.micro ≤ jstar) (z : C.bands.Lists x jstar) (u p : ℕ)
    (hp : p.Prime) (hsmall : (p : ℝ) ≤ x ^ C.theta)
    (hlist : C.bands.listProduct z = groupFreePart (C.bands.groups x) u)
    (hdiv : p ∣ groupFreePart (C.bands.groups x) u) :
    p ∣ microProduct C x jstar z := by
  have hfactor : microProduct C x jstar z * macroProduct C x jstar z =
      groupFreePart (C.bands.groups x) u :=
    (listProduct_eq_micro_mul_macro C x jstar z).symm.trans hlist
  rw [← hfactor] at hdiv
  rcases hp.dvd_mul.mp hdiv with hmicro | hmacro
  · exact hmicro
  · exact (macroProduct_has_no_small_prime C δ x hC hx jstar hj z p hp hsmall hmacro).elim

theorem prime_dvd_groupFreePart_of_not_groups (G : PrimeGroups) (n p : ℕ)
    (hn : n ≠ 0) (hp : p.Prime) (hdiv : p ∣ n)
    (hnot : ∀ g, p ∉ G.primes g) : p ∣ groupFreePart G n := by
  classical
  have hpFactors : p ∈ n.primeFactors := by
    apply Nat.mem_primeFactors.mpr
    exact ⟨hp, hdiv, hn⟩
  have hpNotUnion : p ∉ Finset.univ.biUnion G.primes := by
    intro hpU
    obtain ⟨g, hg⟩ := Finset.mem_biUnion.mp hpU
    exact hnot g hg.2
  have hpMem : p ∈ n.primeFactors \ (Finset.univ.biUnion G.primes) :=
    Finset.mem_sdiff.mpr ⟨hpFactors, hpNotUnion⟩
  have hexp : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hdiv
  have hpPow : p ∣ p ^ n.factorization p := dvd_pow_self p (Nat.ne_of_gt hexp)
  exact dvd_trans hpPow (Finset.dvd_prod_of_mem _ hpMem)

theorem groupFreePart_pos (G : PrimeGroups) (n : ℕ) :
    0 < groupFreePart G n := by
  classical
  unfold groupFreePart
  apply Finset.prod_pos
  intro p hp
  exact Nat.pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).pos

def groupPart (G : PrimeGroups) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors ∩ (Finset.univ.biUnion G.primes), p ^ n.factorization p

def markProduct (G : PrimeGroups) (n : ℕ) (m : MarkChoices G n) : ℕ :=
  ∏ g : Fin G.size, (m g).val

def markImage (G : PrimeGroups) (n : ℕ) (m : MarkChoices G n) : Finset ℕ :=
  Finset.univ.image fun g : Fin G.size => (m g).val

def groupPrimeSet (G : PrimeGroups) : Finset ℕ :=
  Finset.univ.biUnion G.primes

theorem omega_eq_groupPrimeDivisor_card (G : PrimeGroups) (n : ℕ) :
    omega G n = ((groupPrimeSet G).filter fun p => p ∣ n).card := by
  classical
  let family := fun g : Fin G.size => (G.primes g).filter fun p => p ∣ n
  have hdisj : (↑(Finset.univ : Finset (Fin G.size)) : Set (Fin G.size)).PairwiseDisjoint
      family := by
    intro g hg h hh hne
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    exact (Finset.disjoint_left.mp (G.disjoint g h hne))
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1
  have hunion : (Finset.univ : Finset (Fin G.size)).biUnion family =
      (groupPrimeSet G).filter fun p => p ∣ n := by
    ext p
    simp [family, groupPrimeSet, Finset.mem_biUnion, and_assoc, and_left_comm, and_comm]
  have hcard := Finset.card_biUnion hdisj
  rw [hunion] at hcard
  simpa [family, omega, omegaGroup] using hcard.symm

theorem markImage_card (G : PrimeGroups) (n : ℕ) (m : MarkChoices G n) :
    (markImage G n m).card = G.size := by
  classical
  have hinj : Function.Injective (fun g : Fin G.size => (m g).val) := by
    intro g h heq
    by_contra hne
    have hg := (Finset.mem_filter.mp (m g).property).1
    have hh := (Finset.mem_filter.mp (m h).property).1
    have hboth : (m g).val ∈ G.primes g ∩ G.primes h := by
      refine Finset.mem_inter.mpr ⟨hg, ?_⟩
      have heq' : (m g).val = (m h).val := heq
      rw [heq']
      exact hh
    exact (Finset.disjoint_left.mp (G.disjoint g h hne))
      (Finset.mem_inter.mp hboth).1 (Finset.mem_inter.mp hboth).2
  unfold markImage
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem markImage_subset_groupPrimeDivisors (G : PrimeGroups) (n : ℕ)
    (m : MarkChoices G n) :
    markImage G n m ⊆ (groupPrimeSet G).filter fun p => p ∣ n := by
  intro p hp
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hp
  have hopt := Finset.mem_filter.mp (m g).property
  refine Finset.mem_filter.mpr ⟨?_, hopt.2⟩
  exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hopt.1⟩

theorem unmarked_group_divisor_count (G : PrimeGroups) (n : ℕ)
    (m : MarkChoices G n) :
    ((groupPrimeSet G \ markImage G n m).filter fun p => p ∣ n).card =
      omega G n - G.size := by
  classical
  let divisors := (groupPrimeSet G).filter fun p => p ∣ n
  have hmark : markImage G n m ⊆ divisors :=
    markImage_subset_groupPrimeDivisors G n m
  have hfilter :
      (groupPrimeSet G \ markImage G n m).filter (fun p => p ∣ n) =
        divisors \ markImage G n m := by
    ext p
    simp [divisors, Finset.mem_sdiff, Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  have hinter : markImage G n m ∩ divisors = markImage G n m :=
    Finset.inter_eq_left.mpr hmark
  rw [hfilter, Finset.card_sdiff, hinter,
    ← omega_eq_groupPrimeDivisor_card G n, markImage_card]

theorem permission_event_sum_eq_mark_damping (G : PrimeGroups) (n : ℕ)
    (m : MarkChoices G n) (q : ℝ) :
    permissionEventSum (groupPrimeSet G \ markImage G n m) q n =
      q ^ ((omega G n : ℤ) - (G.size : ℤ)) := by
  have hsize : G.size ≤ omega G n := by
    calc
      G.size = (markImage G n m).card := (markImage_card G n m).symm
      _ ≤ ((groupPrimeSet G).filter fun p => p ∣ n).card :=
        Finset.card_le_card (markImage_subset_groupPrimeDivisors G n m)
      _ = omega G n := (omega_eq_groupPrimeDivisor_card G n).symm
  have hcast : ((omega G n : ℤ) - (G.size : ℤ)) =
      ((omega G n - G.size : ℕ) : ℤ) := by
    omega
  rw [permission_event_sum_eq, unmarked_group_divisor_count, hcast]
  simp [zpow_natCast]

theorem markChoiceCoefficient_eq_permission (G : PrimeGroups) (q : ℝ) (n : ℕ)
    (m : MarkChoices G n) :
    markChoiceCoefficient G q n =
      permissionEventSum (groupPrimeSet G \ markImage G n m) q n *
        markBaseCoefficient G n := by
  rw [permission_event_sum_eq_mark_damping]
  rfl

theorem groupFreePart_mul_groupPart (G : PrimeGroups) (n : ℕ) (hn : n ≠ 0) :
    groupFreePart G n * groupPart G n = n := by
  classical
  let U := Finset.univ.biUnion G.primes
  let F := n.primeFactors \ U
  let P := n.primeFactors ∩ U
  have hdisj : Disjoint F P := Finset.disjoint_sdiff_inter _ _
  have hunion : F ∪ P = n.primeFactors := by
    dsimp [F, P]
    exact Finset.sdiff_union_inter _ _
  have hprod : (∏ p ∈ F, p ^ n.factorization p) *
      (∏ p ∈ P, p ^ n.factorization p) =
      ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    rw [← Finset.prod_union hdisj, hunion]
  have hnprod : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    rw [Nat.prod_primeFactors_prod_factorization]
    exact Nat.prod_factorization_pow_eq_self hn
  simpa [groupFreePart, groupPart, F, P, U] using hprod.trans hnprod

theorem markProduct_dvd_groupPart (G : PrimeGroups) (n : ℕ) (hn : n ≠ 0)
    (m : MarkChoices G n) : markProduct G n m ∣ groupPart G n := by
  classical
  let U := Finset.univ.biUnion G.primes
  let P := n.primeFactors ∩ U
  have hinj : Set.InjOn (fun g : Fin G.size => (m g).val)
      (↑(Finset.univ : Finset (Fin G.size)) : Set (Fin G.size)) := by
    intro g hg h hh heq
    by_contra hne
    have hp := Finset.mem_filter.mp (m g).property
    have hq := Finset.mem_filter.mp (m h).property
    have hboth : (m g).val ∈ G.primes g ∩ G.primes h := by
      refine Finset.mem_inter.mpr ⟨hp.1, ?_⟩
      have heq' : (m g).val = (m h).val := heq
      rw [heq']
      exact hq.1
    have hboth' := Finset.mem_inter.mp hboth
    exact (Finset.disjoint_left.mp (G.disjoint g h hne)) hboth'.1 hboth'.2
  have hsubset : markImage G n m ⊆ P := by
    intro p hp
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hp
    have hopt := Finset.mem_filter.mp (m g).property
    have hprime : ((m g).val).Prime :=
      G.prime g (m g).val (Finset.mem_filter.mp (m g).property).1
    have hfactor : (m g).val ∈ n.primeFactors := by
      exact Nat.mem_primeFactors.mpr ⟨hprime, hopt.2, hn⟩
    have hgroup : (m g).val ∈ U := Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hopt.1⟩
    exact Finset.mem_inter.mpr ⟨hfactor, hgroup⟩
  have himage : markProduct G n m = ∏ p ∈ markImage G n m, p := by
    unfold markProduct markImage
    simpa using (Finset.prod_image (f := id) hinj).symm
  have hpow : (∏ p ∈ markImage G n m, p) ∣
      ∏ p ∈ markImage G n m, p ^ n.factorization p := by
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    have hpP : p ∈ P := hsubset hp
    have hpFactor := (Finset.mem_inter.mp hpP).1
    have hpPrime := Nat.prime_of_mem_primeFactors hpFactor
    have hpdvd := (Nat.mem_primeFactors.mp hpFactor).2.1
    have hexp := hpPrime.factorization_pos_of_dvd hn hpdvd
    exact dvd_pow_self p (Nat.ne_of_gt hexp)
  have hsubsetProd : (∏ p ∈ markImage G n m, p ^ n.factorization p) ∣
      ∏ p ∈ P, p ^ n.factorization p :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsubset
  rw [himage]
  exact hpow.trans (by simpa [groupPart, P, U] using hsubsetProd)

theorem assignmentProduct_dvd_index (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar u : ℕ) (z : C.bands.Lists x jstar)
    (m : MarkChoices (C.bands.groups x) u)
    (hu : u ≠ 0)
    (hlist : C.bands.listProduct z = groupFreePart (C.bands.groups x) u) :
    microProduct C x jstar z * markProduct (C.bands.groups x) u m ∣ u := by
  have hmicro : microProduct C x jstar z ∣ groupFreePart (C.bands.groups x) u := by
    exact (microProduct_dvd_listProduct C x jstar z).trans
      (by rw [hlist])
  have hmark : markProduct (C.bands.groups x) u m ∣
      groupPart (C.bands.groups x) u :=
    markProduct_dvd_groupPart (C.bands.groups x) u hu m
  have hprod := Nat.mul_dvd_mul hmicro hmark
  rw [groupFreePart_mul_groupPart (C.bands.groups x) u hu] at hprod
  exact hprod

/-- With one mark per group, `markWeight` is exactly the sum over choices
of a prime divisor from each group. -/
theorem markWeight_eq_markChoices (G : PrimeGroups) (q : ℝ) (n : ℕ) :
    markWeight G q (fun _ => 1) n =
      ∑ z : MarkChoices G n, markChoiceCoefficient G q n := by
  classical
  have hcard (g : Fin G.size) :
      Fintype.card (MarkOptions G n g) = omegaGroup G g n := by
    simp [MarkOptions, omegaGroup]
  have hpi : Fintype.card (MarkChoices G n) =
      ∏ g, omegaGroup G g n := by
    simp [MarkChoices, Fintype.card_pi, hcard]
  have hsum : (∑ z : MarkChoices G n, markChoiceCoefficient G q n) =
      (Fintype.card (MarkChoices G n) : ℝ) * markChoiceCoefficient G q n := by
    simp [markChoiceCoefficient]
  rw [hsum, hpi]
  simp [markWeight, markChoiceCoefficient, Nat.descFactorial, Finset.prod_mul_distrib,
    div_eq_mul_inv, Nat.cast_sum, Nat.cast_prod, omega]
  <;> ring_nf

theorem aQ_eq_sum_lists (B : Erdos821.Blueprint.BandData) (x : ℝ) (jstar v : ℕ) :
    B.aQ x jstar v =
      ∑ z : B.Lists x jstar,
        if B.listProduct z = v then listNormalizer B x else 0 := by
  classical
  let P : B.Lists x jstar → Prop := fun z => B.listProduct z = v
  have hcard : (Finset.univ.filter P).card =
      ∑ z : B.Lists x jstar, if P z then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp [Finset.sum_filter, P]
  have hcardR : ((Finset.univ.filter P).card : ℝ) =
      ∑ z : B.Lists x jstar, if P z then (1 : ℝ) else 0 := by
    exact_mod_cast hcard
  rw [Erdos821.Blueprint.BandData.aQ, hcardR]
  simp only [listNormalizer]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : B.listProduct z = v <;> simp [P, h]

theorem bandWeight_eq_assignment_sum (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar u : ℕ) (hell : C.bands.geometry.ell = 1) :
    C.bands.weight x jstar u =
      ∑ z : C.bands.Lists x jstar,
        if C.bands.listProduct z = groupFreePart (C.bands.groups x) u then
          listNormalizer C.bands x *
            markWeight (C.bands.groups x) C.bands.geometry.q (fun _ => 1) u
        else 0 := by
  rw [Erdos821.Blueprint.BandData.weight, hell, aQ_eq_sum_lists]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : C.bands.listProduct z = groupFreePart (C.bands.groups x) u
  · simp [h, listNormalizer, markChoiceCoefficient, mul_assoc]
  · simp [h]

theorem bandWeight_eq_double_assignment_sum (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar u : ℕ) (hell : C.bands.geometry.ell = 1) :
    C.bands.weight x jstar u =
      ∑ z : C.bands.Lists x jstar,
        ∑ m : MarkChoices (C.bands.groups x) u,
          if C.bands.listProduct z = groupFreePart (C.bands.groups x) u then
            listNormalizer C.bands x *
              markChoiceCoefficient (C.bands.groups x) C.bands.geometry.q u
          else 0 := by
  rw [bandWeight_eq_assignment_sum C x jstar u hell, markWeight_eq_markChoices]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : C.bands.listProduct z = groupFreePart (C.bands.groups x) u
  · simp only [if_pos h]
    change listNormalizer C.bands x *
        (∑ m ∈ Finset.univ,
          markChoiceCoefficient (C.bands.groups x) C.bands.geometry.q u) = _
    rw [Finset.mul_sum]
  · simp [h]

theorem ofFn_count_eq_fin_count {k : ℕ} (f : Fin k → ℕ) (p : ℕ) :
    List.count p (List.ofFn f) = Fin.countP (fun i => decide (f i = p)) := by
  classical
  simp only [List.count, List.ofFn_eq_map, List.countP_map]
  have hpred : (fun x => x == p) ∘ f = fun i => decide (f i = p) := by
    funext i
    by_cases h : f i = p <;> simp [h]
  rw [hpred]
  exact (Fin.countP_eq_countP_map_finRange _).symm

theorem fin_sum_eq_univ_sum_nat {k : ℕ} (f : Fin k → ℕ) :
    Fin.sum f = ∑ i : Fin k, f i := by
  induction k with
  | zero => simp [Fin.sum]
  | succ k ih =>
    rw [Fin.sum_succ, Fin.sum_univ_succ, ih]

theorem primeTuple_prod_eq_perm {k : ℕ} {f g : Fin k → ℕ}
    (hf : ∀ i, (f i).Prime) (hg : ∀ i, (g i).Prime)
    (hprod : (∏ i : Fin k, f i) = ∏ i : Fin k, g i) :
    List.Perm (List.ofFn f) (List.ofFn g) := by
  classical
  have hfac : (∏ i : Fin k, f i).factorization =
      (∏ i : Fin k, g i).factorization := congrArg Nat.factorization hprod
  have hfactorF : ∀ p, (∏ i : Fin k, f i).factorization p =
      Fin.countP (fun i => decide (f i = p)) := by
    intro p
    rw [Nat.factorization_prod (S := Finset.univ) (g := f) (by
      intro i hi
      exact (hf i).ne_zero)]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    calc
      (∑ i : Fin k, (f i).factorization p) =
          ∑ i : Fin k, (decide (f i = p)).toNat := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.Prime.factorization (hf i)]
        by_cases h : p = f i <;> simp [Finsupp.single_apply, h, eq_comm]
      _ = Fin.countP (fun i => decide (f i = p)) := by
        rw [← fin_sum_eq_univ_sum_nat]
        rfl
  have hfactorG : ∀ p, (∏ i : Fin k, g i).factorization p =
      Fin.countP (fun i => decide (g i = p)) := by
    intro p
    rw [Nat.factorization_prod (S := Finset.univ) (g := g) (by
      intro i hi
      exact (hg i).ne_zero)]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    calc
      (∑ i : Fin k, (g i).factorization p) =
          ∑ i : Fin k, (decide (g i = p)).toNat := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.Prime.factorization (hg i)]
        by_cases h : p = g i <;> simp [Finsupp.single_apply, h, eq_comm]
      _ = Fin.countP (fun i => decide (g i = p)) := by
        rw [← fin_sum_eq_univ_sum_nat]
        rfl
  apply List.perm_iff_count.mpr
  intro p
  rw [ofFn_count_eq_fin_count, ← hfactorF p, hfac, hfactorG p,
    ← ofFn_count_eq_fin_count]

theorem primeTuple_fiber_card_le_factorial {k : ℕ} (t : Fin k → ℕ)
    (F : Finset (Fin k → ℕ))
    (ht : ∀ i, (t i).Prime)
    (hprime : ∀ f ∈ F, ∀ i, (f i).Prime)
    (hprod : ∀ f ∈ F, (∏ i, f i) = ∏ i, t i) :
    F.card ≤ k.factorial := by
  classical
  let image := F.image List.ofFn
  have hinj : Function.Injective (List.ofFn : (Fin k → ℕ) → List ℕ) := List.ofFn_injective
  have hcard : F.card = image.card := by
    dsimp [image]
    exact (Finset.card_image_of_injective F hinj).symm
  have himage : image ⊆ (List.ofFn t).permutations.toFinset := by
    intro l hl
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hl
    have hp := primeTuple_prod_eq_perm (hprime f hf) ht (hprod f hf)
    simp only [List.mem_toFinset, List.mem_permutations]
    exact hp
  calc
    F.card = image.card := hcard
    _ ≤ ((List.ofFn t).permutations.toFinset).card := Finset.card_le_card himage
    _ ≤ (List.ofFn t).permutations.length := List.toFinset_card_le _
    _ = k.factorial := by simp [List.length_permutations]

abbrev MacroSlotIndex (C : Erdos821.Blueprint.CandidateData) :=
  Fin C.micro × Fin C.bands.r₀

abbrev MacroAssignments (C : Erdos821.Blueprint.CandidateData) (x : ℝ) :=
  (s : MacroSlotIndex C) →
    {p : ℕ // p ∈ C.bands.band x s.1.val}

abbrev MacroSlotSubtype (C : Erdos821.Blueprint.CandidateData) (x : ℝ) :=
  {s : C.bands.Slot x // s ∈ macroSlots C x}

abbrev MicroSlotSubtype (C : Erdos821.Blueprint.CandidateData) (x : ℝ) :=
  {s : C.bands.Slot x // s ∈ microSlots C x}

abbrev MicroAssignments (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ) :=
  (s : MicroSlotSubtype C x) → C.bands.SlotValue x jstar s.val

def microAssignmentProduct (C : Erdos821.Blueprint.CandidateData) (x : ℝ)
    (jstar : ℕ) (m : MicroAssignments C x jstar) : ℕ :=
  ∏ s, (m s).val

def microCapturesSmallFreePrimes (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar u : ℕ) (m : MicroAssignments C x jstar) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ C.theta →
    p ∉ groupPrimeSet (C.bands.groups x) → p ∣ u →
      p ∣ microAssignmentProduct C x jstar m

theorem microMarkProduct_dvd_index (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (u : ℕ) (hu : u ≠ 0)
    (jstar : ℕ) (m : MicroAssignments C x jstar)
    (marks : MarkChoices (C.bands.groups x) u)
    (hmicro : microAssignmentProduct C x jstar m ∣
      groupFreePart (C.bands.groups x) u) :
    microAssignmentProduct C x jstar m *
      markProduct (C.bands.groups x) u marks ∣ u := by
  have hmark := markProduct_dvd_groupPart (C.bands.groups x) u hu marks
  have hprod := Nat.mul_dvd_mul hmicro hmark
  rw [groupFreePart_mul_groupPart (C.bands.groups x) u hu] at hprod
  exact hprod


def microRestriction (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ)
    (z : C.bands.Lists x jstar) : MicroAssignments C x jstar :=
  fun s => z s.val

theorem microProduct_eq_restriction_product (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (z : C.bands.Lists x jstar) :
    microProduct C x jstar z =
      ∏ s : MicroSlotSubtype C x, (microRestriction C x jstar z s).val := by
  classical
  change (∏ s ∈ microSlots C x, (z s).val) = _
  exact (Finset.prod_attach (microSlots C x) (fun s => (z s).val)).symm


theorem micro_assignment_reciprocal_sum (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) :
    (∑ m : MicroAssignments C x jstar,
      ∏ s : MicroSlotSubtype C x, ((m s).val : ℝ)⁻¹) =
      ∏ s : MicroSlotSubtype C x,
        ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹) := by
  classical
  unfold MicroAssignments
  exact (Fintype.prod_sum
    (κ := fun s : MicroSlotSubtype C x => C.bands.SlotValue x jstar s.val)
    (f := fun s v => ((v.val : ℝ)⁻¹))).symm



theorem micro_assignment_product_inv (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (m : MicroAssignments C x jstar) :
    ((microAssignmentProduct C x jstar m : ℝ)⁻¹) =
      ∏ s : MicroSlotSubtype C x, ((m s).val : ℝ)⁻¹ := by
  simp [microAssignmentProduct, Nat.cast_prod, Finset.prod_inv_distrib]

theorem micro_assignment_harmonic_mass (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) :
    (∑ m : MicroAssignments C x jstar,
      (microAssignmentProduct C x jstar m : ℝ)⁻¹) =
      ∏ s : MicroSlotSubtype C x,
        ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹) := by
  classical
  calc
    (∑ m : MicroAssignments C x jstar,
        (microAssignmentProduct C x jstar m : ℝ)⁻¹) =
        ∑ m : MicroAssignments C x jstar,
          ∏ s : MicroSlotSubtype C x, ((m s).val : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro m hm
      exact micro_assignment_product_inv C x jstar m
    _ = ∏ s : MicroSlotSubtype C x,
        ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹) :=
      micro_assignment_reciprocal_sum C x jstar


theorem microRestriction_captures_small_free_prime
    (C : Erdos821.Blueprint.CandidateData) (δ x : ℝ)
    (hC : C.Geometry δ) (hx : 1 < x) (jstar : ℕ)
    (hj : C.micro ≤ jstar) (z : C.bands.Lists x jstar) (u p : ℕ)
    (hp : p.Prime) (hsmall : (p : ℝ) ≤ x ^ C.theta)
    (hlist : C.bands.listProduct z = groupFreePart (C.bands.groups x) u)
    (hu : u ≠ 0) (hdiv : p ∣ u) (hnot : p ∉ groupPrimeSet (C.bands.groups x)) :
    p ∣ microAssignmentProduct C x jstar (microRestriction C x jstar z) := by
  have hnotGroups : ∀ g, p ∉ (C.bands.groups x).primes g := by
    intro g hpG
    exact hnot (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hpG⟩)
  have hfree : p ∣ groupFreePart (C.bands.groups x) u :=
    prime_dvd_groupFreePart_of_not_groups (C.bands.groups x) u p hu
      hp hdiv hnotGroups
  have hmicro := small_groupFree_prime_divides_micro C δ x hC hx jstar hj z u p
    hp hsmall hlist hfree
  have hrestrict : microAssignmentProduct C x jstar
        (microRestriction C x jstar z) = microProduct C x jstar z := by
    simpa [microAssignmentProduct] using
      (microProduct_eq_restriction_product C x jstar z).symm
  rw [hrestrict]
  exact hmicro



def macroFinIndex (C : Erdos821.Blueprint.CandidateData) (x : ℝ)
    (hbound : C.micro ≤ C.bands.last x + 1) (j : Fin C.micro) :
    Fin (C.bands.last x + 1) :=
  ⟨j.val, Nat.lt_of_lt_of_le j.isLt hbound⟩

noncomputable def macroSlotEquiv (C : Erdos821.Blueprint.CandidateData) (x : ℝ)
    (hbound : C.micro ≤ C.bands.last x + 1) :
    MacroSlotSubtype C x ≃ MacroSlotIndex C where
  toFun s :=
    (⟨s.val.1.val, (Finset.mem_filter.mp s.property).2⟩, s.val.2)
  invFun m :=
    ⟨(macroFinIndex C x hbound m.1, m.2),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, m.1.isLt⟩⟩
  left_inv s := by
    apply Subtype.ext
    rcases s with ⟨⟨⟨j, hj⟩, i⟩, hs⟩
    rfl
  right_inv m := by
    rcases m with ⟨j, i⟩
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl

def macroRestriction (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ)
    (z : C.bands.Lists x jstar) (hbound : C.micro ≤ C.bands.last x + 1)
    (hj : C.micro ≤ jstar) : MacroAssignments C x :=
  fun s => by
    let slot : C.bands.Slot x := (macroFinIndex C x hbound s.1, s.2)
    have hslot : slot ∈ macroSlots C x := by
      simp [slot, macroSlots, macroFinIndex]
    exact ⟨(z slot).val, macro_slot_mem_band C x jstar z slot hslot hj⟩

def macroAssignmentProduct (C : Erdos821.Blueprint.CandidateData) (x : ℝ)
    (m : MacroAssignments C x) : ℕ :=
  ∏ s, (m s).val

theorem macroProduct_eq_restriction_product (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (z : C.bands.Lists x jstar)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar) :
    macroProduct C x jstar z = macroAssignmentProduct C x
      (macroRestriction C x jstar z hbound hj) := by
  classical
  let e := macroSlotEquiv C x hbound
  have hattach : macroProduct C x jstar z =
      ∏ s : MacroSlotSubtype C x, (z s.val).val := by
    dsimp [macroProduct]
    exact (Finset.prod_attach (macroSlots C x) (fun s => (z s).val)).symm
  rw [hattach]
  exact Fintype.prod_equiv e
    (fun s : MacroSlotSubtype C x => (z s.val).val)
    (fun m : MacroSlotIndex C =>
      (macroRestriction C x jstar z hbound hj m).val)
    (by
      intro s
      have hidx : macroFinIndex C x hbound (e s).1 = s.val.1 := by
        apply Fin.ext
        rfl
      have hslot : (macroFinIndex C x hbound (e s).1, (e s).2) = s.val := by
        exact Prod.ext hidx rfl
      change (z s.val).val =
        (z (macroFinIndex C x hbound (e s).1, (e s).2)).val
      rw [hslot])

theorem macroRestriction_eval (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (z : C.bands.Lists x jstar)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (s : MacroSlotSubtype C x) :
    (macroRestriction C x jstar z hbound hj (macroSlotEquiv C x hbound s)).val =
      (z s.val).val := by
  let e := macroSlotEquiv C x hbound
  have hidx : macroFinIndex C x hbound (e s).1 = s.val.1 := by
    apply Fin.ext
    rfl
  have hslot : (macroFinIndex C x hbound (e s).1, (e s).2) = s.val :=
    Prod.ext hidx rfl
  change (z (macroFinIndex C x hbound (e s).1, (e s).2)).val = _
  rw [hslot]

def macroCompletionFiber (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (hbound : C.micro ≤ C.bands.last x + 1)
    (hj : C.micro ≤ jstar) (m : MicroAssignments C x jstar) (n : ℕ) :
    Finset (C.bands.Lists x jstar) :=
  Finset.univ.filter fun z => microRestriction C x jstar z = m ∧
    C.bands.listProduct z = n

theorem macroProduct_eq_of_same_micro (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (z₁ z₂ : C.bands.Lists x jstar)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (hmicro : microRestriction C x jstar z₁ = microRestriction C x jstar z₂)
    (hfull : C.bands.listProduct z₁ = C.bands.listProduct z₂)
    (hnz : C.bands.listProduct z₁ ≠ 0) :
    macroProduct C x jstar z₁ = macroProduct C x jstar z₂ := by
  have hmicroProd : microProduct C x jstar z₁ = microProduct C x jstar z₂ := by
    rw [microProduct_eq_restriction_product, microProduct_eq_restriction_product, hmicro]
  have hfactor₁ := listProduct_eq_micro_mul_macro C x jstar z₁
  have hfactor₂ := listProduct_eq_micro_mul_macro C x jstar z₂
  have hpos : 0 < microProduct C x jstar z₁ := by
    have hne : microProduct C x jstar z₁ ≠ 0 := by
      intro hzero
      apply hnz
      rw [hfactor₁, hzero, Nat.zero_mul]
    exact Nat.pos_of_ne_zero hne
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    microProduct C x jstar z₁ * macroProduct C x jstar z₁ =
        C.bands.listProduct z₁ := hfactor₁.symm
    _ = C.bands.listProduct z₂ := hfull
    _ = microProduct C x jstar z₂ * macroProduct C x jstar z₂ := hfactor₂
    _ = microProduct C x jstar z₁ * macroProduct C x jstar z₂ := by rw [hmicroProd]

theorem macroAssignment_fiber_card_le_factorial
    (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (n : ℕ) :
    (Finset.univ.filter fun m : MacroAssignments C x =>
      macroAssignmentProduct C x m = n).card ≤
        (Fintype.card (MacroSlotIndex C)).factorial := by
  classical
  let α := MacroSlotIndex C
  let k := Fintype.card α
  let e : Fin k ≃ α := (Fintype.equivFin α).symm
  let tuple (m : MacroAssignments C x) (i : Fin k) : ℕ := (m (e i)).val
  let fiber := Finset.univ.filter fun m : MacroAssignments C x =>
    macroAssignmentProduct C x m = n
  change fiber.card ≤ k.factorial
  by_cases hne : fiber.Nonempty
  · obtain ⟨m₀, hm₀⟩ := hne
    let image := fiber.image (fun m => tuple m)
    have hinj : Function.Injective tuple := by
      intro m₁ m₂ h
      funext s
      obtain ⟨i, hi⟩ := e.surjective s
      have hv : (m₁ (e i)).val = (m₂ (e i)).val := by
        change tuple m₁ i = tuple m₂ i
        exact congrFun h i
      have hv' : (m₁ s).val = (m₂ s).val := by
        calc
          (m₁ s).val = (m₁ (e i)).val := by rw [← hi]
          _ = (m₂ (e i)).val := hv
          _ = (m₂ s).val := by rw [hi]
      exact Subtype.ext hv'
    have hcard : fiber.card = image.card := by
      dsimp [image]
      exact (Finset.card_image_of_injective fiber hinj).symm
    have ht : ∀ i, (tuple m₀ i).Prime := by
      intro i
      exact (Finset.mem_filter.mp (m₀ (e i)).property).2
    have hprime : ∀ f ∈ image, ∀ i, (f i).Prime := by
      intro f hf i
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hf
      exact (Finset.mem_filter.mp (m (e i)).property).2
    have hprod : ∀ f ∈ image, (∏ i, f i) = ∏ i, tuple m₀ i := by
      intro f hf
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hf
      have hmFiber := (Finset.mem_filter.mp hm).2
      have hm₀Fiber := (Finset.mem_filter.mp hm₀).2
      have hprod_m : (∏ i, tuple m i) = macroAssignmentProduct C x m := by
        simpa [tuple, macroAssignmentProduct, α, Equiv.prod_comp] using
          (Equiv.prod_comp e (fun s : α => (m s).val))
      have hprod₀ : (∏ i, tuple m₀ i) = macroAssignmentProduct C x m₀ := by
        simpa [tuple, macroAssignmentProduct, α, Equiv.prod_comp] using
          (Equiv.prod_comp e (fun s : α => (m₀ s).val))
      calc
        (∏ i, tuple m i) = macroAssignmentProduct C x m := hprod_m
        _ = n := hmFiber
        _ = macroAssignmentProduct C x m₀ := hm₀Fiber.symm
        _ = ∏ i, tuple m₀ i := hprod₀.symm
    have hbound := primeTuple_fiber_card_le_factorial (tuple m₀) image ht hprime hprod
    rw [← hcard] at hbound
    simpa [α, k] using hbound
  · have hempty : fiber = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      exact hne ⟨m, hm⟩
    simp [hempty]

theorem macroCompletionFiber_card_le_factorial
    (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (m : MicroAssignments C x jstar) (n : ℕ) (hn : n ≠ 0) :
    (macroCompletionFiber C x jstar hbound hj m n).card ≤
      (Fintype.card (MacroSlotIndex C)).factorial := by
  classical
  let fiber := macroCompletionFiber C x jstar hbound hj m n
  change fiber.card ≤ (Fintype.card (MacroSlotIndex C)).factorial
  by_cases hne : fiber.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    let restrict := fun z : C.bands.Lists x jstar =>
      macroRestriction C x jstar z hbound hj
    let image := fiber.image restrict
    have hinj : Set.InjOn restrict (↑fiber : Set (C.bands.Lists x jstar)) := by
      intro z₁ hz₁ z₂ hz₂ hEq
      have hp₁ := (Finset.mem_filter.mp hz₁).2.1
      have hp₂ := (Finset.mem_filter.mp hz₂).2.1
      have hmicro : microRestriction C x jstar z₁ = microRestriction C x jstar z₂ :=
        hp₁.trans hp₂.symm
      funext s
      by_cases hs : s ∈ microSlots C x
      · exact congrFun hmicro ⟨s, hs⟩
      · have hpart := micro_macro_slots_partition C x
        have hsUnion : s ∈ microSlots C x ∪ macroSlots C x := by
          rw [hpart.2]
          exact Finset.mem_univ _
        rcases Finset.mem_union.mp hsUnion with hmicroS | hmacroS
        · exact (hs hmicroS).elim
        · let ms : MacroSlotSubtype C x := ⟨s, hmacroS⟩
          let e := macroSlotEquiv C x hbound
          let q := e ms
          have hval := congrArg Subtype.val (congrFun hEq q)
          rw [macroRestriction_eval C x jstar z₁ hbound hj ms] at hval
          rw [macroRestriction_eval C x jstar z₂ hbound hj ms] at hval
          exact Subtype.ext hval
    have hcard : fiber.card = image.card :=
      (Finset.card_image_of_injOn hinj).symm
    let macroFiber := Finset.univ.filter fun q : MacroAssignments C x =>
      macroAssignmentProduct C x q = macroProduct C x jstar z₀
    have himage : image ⊆ macroFiber := by
      intro q hq
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
      have hp := (Finset.mem_filter.mp hz).2
      have hp₀ := (Finset.mem_filter.mp hz₀).2
      have hmacroEq := macroProduct_eq_of_same_micro C x jstar z z₀ hbound hj
        (hp.1.trans hp₀.1.symm) (by rw [hp.2, hp₀.2])
        (by rw [hp.2]; exact hn)
      have hassignment : macroAssignmentProduct C x (restrict z) =
          macroProduct C x jstar z₀ := by
        exact (macroProduct_eq_restriction_product C x jstar z hbound hj).symm.trans hmacroEq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hassignment⟩
    have hmacroBound := macroAssignment_fiber_card_le_factorial C x
      (macroProduct C x jstar z₀)
    calc
      fiber.card = image.card := hcard
      _ ≤ macroFiber.card := Finset.card_le_card himage
      _ = (Finset.univ.filter fun q : MacroAssignments C x =>
          macroAssignmentProduct C x q = macroProduct C x jstar z₀).card := rfl
      _ ≤ (Fintype.card (MacroSlotIndex C)).factorial := hmacroBound
  · have hempty : fiber = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hne ⟨z, hz⟩
    rw [hempty]
    simp


theorem listFiber_card_le_micro_divisor_count
    (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (v : ℕ) (hv : v ≠ 0) :
    (Finset.univ.filter fun z : C.bands.Lists x jstar =>
      C.bands.listProduct z = v).card ≤
      (Fintype.card (MacroSlotIndex C)).factorial *
        (Finset.univ.filter fun m : MicroAssignments C x jstar =>
          microAssignmentProduct C x jstar m ∣ v).card := by
  classical
  let fiber := Finset.univ.filter fun z : C.bands.Lists x jstar =>
    C.bands.listProduct z = v
  let divisorAssignments := Finset.univ.filter fun m : MicroAssignments C x jstar =>
    microAssignmentProduct C x jstar m ∣ v
  have hcard : fiber.card =
      ∑ m ∈ Finset.univ,
        (fiber.filter fun z => microRestriction C x jstar z = m).card := by
    simpa [fiber] using
      (Finset.card_eq_sum_card_fiberwise
        (f := fun z : C.bands.Lists x jstar => microRestriction C x jstar z)
        (s := fiber) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _))
  have hsum :
      (∑ m ∈ Finset.univ,
        (fiber.filter fun z => microRestriction C x jstar z = m).card) ≤
      ∑ m ∈ Finset.univ,
        if microAssignmentProduct C x jstar m ∣ v then
          (Fintype.card (MacroSlotIndex C)).factorial else 0 := by
    apply Finset.sum_le_sum
    intro m hm
    by_cases hdiv : microAssignmentProduct C x jstar m ∣ v
    · have hsub : fiber.filter (fun z => microRestriction C x jstar z = m) ⊆
          macroCompletionFiber C x jstar hbound hj m v := by
        intro z hz
        have hzF := (Finset.mem_filter.mp hz).1
        have hzm := (Finset.mem_filter.mp hz).2
        have hprod := (Finset.mem_filter.mp hzF).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hzm, hprod⟩⟩
      rw [if_pos hdiv]
      exact (Finset.card_le_card hsub).trans
        (macroCompletionFiber_card_le_factorial C x jstar hbound hj m v hv)
    · have hempty : fiber.filter (fun z => microRestriction C x jstar z = m) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzF := (Finset.mem_filter.mp hz).1
        have hzm := (Finset.mem_filter.mp hz).2
        have hprod := (Finset.mem_filter.mp hzF).2
        have hmicro : microAssignmentProduct C x jstar m =
            microProduct C x jstar z := by
          rw [← hzm]
          simpa [microAssignmentProduct] using
            (microProduct_eq_restriction_product C x jstar z).symm
        have hdvd : microProduct C x jstar z ∣ v := by
          have hdivList := microProduct_dvd_listProduct C x jstar z
          rw [hprod] at hdivList
          exact hdivList
        have hdvd : microAssignmentProduct C x jstar m ∣ v := by
          rw [hmicro]
          exact hdvd
        exact hdiv hdvd
      simp [hempty, hdiv]
  calc
    fiber.card =
        ∑ m ∈ Finset.univ,
          (fiber.filter fun z => microRestriction C x jstar z = m).card := hcard
    _ ≤ ∑ m ∈ Finset.univ,
          if microAssignmentProduct C x jstar m ∣ v then
            (Fintype.card (MacroSlotIndex C)).factorial else 0 := hsum
    _ = (Fintype.card (MacroSlotIndex C)).factorial * divisorAssignments.card := by
      change (∑ m ∈ Finset.univ,
        if microAssignmentProduct C x jstar m ∣ v then
          (Fintype.card (MacroSlotIndex C)).factorial else 0) = _
      rw [← Finset.sum_filter]
      simp [divisorAssignments, Nat.mul_comm]



theorem listFiber_card_le_captured_micro_count
    (C : Erdos821.Blueprint.CandidateData) (δ x : ℝ)
    (hC : C.Geometry δ) (hx : 1 < x) (jstar : ℕ)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (u : ℕ) (hu : u ≠ 0) :
    (Finset.univ.filter fun z : C.bands.Lists x jstar =>
      C.bands.listProduct z = groupFreePart (C.bands.groups x) u).card ≤
      (Fintype.card (MacroSlotIndex C)).factorial *
        (Finset.univ.filter fun m : MicroAssignments C x jstar =>
          microAssignmentProduct C x jstar m ∣ groupFreePart (C.bands.groups x) u ∧
            microCapturesSmallFreePrimes C x jstar u m).card := by
  classical
  let v := groupFreePart (C.bands.groups x) u
  let fiber := Finset.univ.filter fun z : C.bands.Lists x jstar =>
    C.bands.listProduct z = v
  let goodAssignments := Finset.univ.filter fun m : MicroAssignments C x jstar =>
    microAssignmentProduct C x jstar m ∣ v ∧ microCapturesSmallFreePrimes C x jstar u m
  have hcard : fiber.card =
      ∑ m ∈ Finset.univ,
        (fiber.filter fun z => microRestriction C x jstar z = m).card := by
    simpa [fiber] using
      (Finset.card_eq_sum_card_fiberwise
        (f := fun z : C.bands.Lists x jstar => microRestriction C x jstar z)
        (s := fiber) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _))
  have hsum :
      (∑ m ∈ Finset.univ,
        (fiber.filter fun z => microRestriction C x jstar z = m).card) ≤
      ∑ m ∈ Finset.univ,
        if microAssignmentProduct C x jstar m ∣ v ∧
            microCapturesSmallFreePrimes C x jstar u m then
          (Fintype.card (MacroSlotIndex C)).factorial else 0 := by
    apply Finset.sum_le_sum
    intro m hm
    by_cases hgood : microAssignmentProduct C x jstar m ∣ v ∧
        microCapturesSmallFreePrimes C x jstar u m
    · have hsub : fiber.filter (fun z => microRestriction C x jstar z = m) ⊆
          macroCompletionFiber C x jstar hbound hj m v := by
        intro z hz
        have hzF := (Finset.mem_filter.mp hz).1
        have hzm := (Finset.mem_filter.mp hz).2
        have hprod := (Finset.mem_filter.mp hzF).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hzm, hprod⟩⟩
      rw [if_pos hgood]
      exact (Finset.card_le_card hsub).trans
        (macroCompletionFiber_card_le_factorial C x jstar hbound hj m v
          (Nat.ne_of_gt (groupFreePart_pos (C.bands.groups x) u)))
    · have hempty : fiber.filter (fun z => microRestriction C x jstar z = m) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzF := (Finset.mem_filter.mp hz).1
        have hzm := (Finset.mem_filter.mp hz).2
        have hprod := (Finset.mem_filter.mp hzF).2
        have hmicroEq : microAssignmentProduct C x jstar m = microProduct C x jstar z := by
          rw [← hzm]
          simpa [microAssignmentProduct] using
            (microProduct_eq_restriction_product C x jstar z).symm
        have hdiv : microAssignmentProduct C x jstar m ∣ v := by
          have hdivz := microProduct_dvd_listProduct C x jstar z
          rw [hprod] at hdivz
          rw [hmicroEq]
          exact hdivz
        have hcapture : microCapturesSmallFreePrimes C x jstar u m := by
          intro p hp hsmall hnot hpdiv
          have hcap := microRestriction_captures_small_free_prime C δ x hC hx
            jstar hj z u p hp hsmall hprod hu hpdiv hnot
          rw [hzm] at hcap
          exact hcap
        exact hgood ⟨hdiv, hcapture⟩
      simp [hempty, hgood]
  calc
    fiber.card =
        ∑ m ∈ Finset.univ,
          (fiber.filter fun z => microRestriction C x jstar z = m).card := hcard
    _ ≤ ∑ m ∈ Finset.univ,
          if microAssignmentProduct C x jstar m ∣ v ∧
              microCapturesSmallFreePrimes C x jstar u m then
            (Fintype.card (MacroSlotIndex C)).factorial else 0 := hsum
    _ = (Fintype.card (MacroSlotIndex C)).factorial * goodAssignments.card := by
      change (∑ m ∈ Finset.univ,
        if microAssignmentProduct C x jstar m ∣ v ∧
            microCapturesSmallFreePrimes C x jstar u m then
          (Fintype.card (MacroSlotIndex C)).factorial else 0) = _
      rw [← Finset.sum_filter]
      simp [goodAssignments, Nat.mul_comm]

theorem aQ_le_captured_micro_assignments
    (C : Erdos821.Blueprint.CandidateData) (δ x : ℝ) (jstar u : ℕ)
    (hC : C.Geometry δ) (hx : 1 < x)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (hu : u ≠ 0) :
    C.bands.aQ x jstar (groupFreePart (C.bands.groups x) u) ≤
      listNormalizer C.bands x * (Fintype.card (MacroSlotIndex C)).factorial *
        ((Finset.univ.filter fun m : MicroAssignments C x jstar =>
          microAssignmentProduct C x jstar m ∣ groupFreePart (C.bands.groups x) u ∧
            microCapturesSmallFreePrimes C x jstar u m).card : ℝ) := by
  classical
  let v := groupFreePart (C.bands.groups x) u
  let fiber := Finset.univ.filter fun z : C.bands.Lists x jstar =>
    C.bands.listProduct z = v
  let goodAssignments := Finset.univ.filter fun m : MicroAssignments C x jstar =>
    microAssignmentProduct C x jstar m ∣ v ∧ microCapturesSmallFreePrimes C x jstar u m
  have hcard := listFiber_card_le_captured_micro_count C δ x hC hx jstar
    hbound hj u hu
  have hcardR : (fiber.card : ℝ) ≤
      ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) * goodAssignments.card := by
    exact_mod_cast hcard
  have hnorm : 0 ≤ listNormalizer C.bands x := by
    unfold listNormalizer
    exact inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  calc
    C.bands.aQ x jstar v = listNormalizer C.bands x * (fiber.card : ℝ) := by
      simp [fiber, Erdos821.Blueprint.BandData.aQ, listNormalizer]
    _ ≤ listNormalizer C.bands x *
          ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) * goodAssignments.card := by
      calc
        listNormalizer C.bands x * (fiber.card : ℝ) ≤
            listNormalizer C.bands x *
              (((Fintype.card (MacroSlotIndex C)).factorial : ℝ) * goodAssignments.card) :=
          mul_le_mul_of_nonneg_left hcardR hnorm
        _ = listNormalizer C.bands x *
              ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) * goodAssignments.card := by ring

theorem bandWeight_le_captured_assignment_mask
    (C : Erdos821.Blueprint.CandidateData) (δ x : ℝ) (jstar u : ℕ)
    (hC : C.Geometry δ) (hx : 1 < x)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (hu : u ≠ 0) (hell : C.bands.geometry.ell = 1)
    (hq : 0 < C.bands.geometry.q)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g) :
    C.bands.weight x jstar u ≤
      ∑ m ∈ (Finset.univ.filter fun m : MicroAssignments C x jstar =>
          microAssignmentProduct C x jstar m ∣
            groupFreePart (C.bands.groups x) u ∧
          microCapturesSmallFreePrimes C x jstar u m),
        ∑ marks : MarkChoices (C.bands.groups x) u,
          (listNormalizer C.bands x *
            (Fintype.card (MacroSlotIndex C)).factorial) *
            markBaseCoefficient (C.bands.groups x) u *
            permissionEventSum
              (groupPrimeSet (C.bands.groups x) \ markImage (C.bands.groups x) u marks)
              C.bands.geometry.q u := by
  classical
  let G := C.bands.groups x
  let goodAssignments := Finset.univ.filter fun m : MicroAssignments C x jstar =>
    microAssignmentProduct C x jstar m ∣ groupFreePart G u ∧
      microCapturesSmallFreePrimes C x jstar u m
  let K := listNormalizer C.bands x * (Fintype.card (MacroSlotIndex C)).factorial
  have haQ := aQ_le_captured_micro_assignments C δ x jstar u hC hx hbound hj hu
  have hmarkNonneg : 0 ≤ markWeight G C.bands.geometry.q (fun _ => 1) u := by
    unfold markWeight
    apply mul_nonneg
    · exact zpow_nonneg hq.le _
    · apply Finset.prod_nonneg
      intro g hg
      have hmg := hmass g
      positivity
  have hsumEq :
      (∑ m ∈ goodAssignments,
        ∑ marks : MarkChoices G u,
          K * markBaseCoefficient G u *
            permissionEventSum (groupPrimeSet G \ markImage G u marks)
              C.bands.geometry.q u) =
        K * (goodAssignments.card : ℝ) *
          markWeight G C.bands.geometry.q (fun _ => 1) u := by
    calc
      _ = ∑ m ∈ goodAssignments,
            K * (∑ marks : MarkChoices G u,
              markChoiceCoefficient G C.bands.geometry.q u) := by
        apply Finset.sum_congr rfl
        intro m hm
        calc
          (∑ marks : MarkChoices G u,
              K * markBaseCoefficient G u *
                permissionEventSum (groupPrimeSet G \ markImage G u marks)
                  C.bands.geometry.q u) =
              ∑ marks : MarkChoices G u,
                K * markChoiceCoefficient G C.bands.geometry.q u := by
            apply Finset.sum_congr rfl
            intro marks hmarks
            rw [markChoiceCoefficient_eq_permission]
            ring
          _ = K * (∑ marks : MarkChoices G u,
                markChoiceCoefficient G C.bands.geometry.q u) := by
            rw [Finset.mul_sum]
      _ = K * (goodAssignments.card : ℝ) *
            markWeight G C.bands.geometry.q (fun _ => 1) u := by
        rw [markWeight_eq_markChoices]
        simp [Finset.sum_const, mul_assoc]
        <;> ring
  have hAqmul :
      C.bands.aQ x jstar (groupFreePart G u) *
          markWeight G C.bands.geometry.q (fun _ => 1) u ≤
        K * (goodAssignments.card : ℝ) *
          markWeight G C.bands.geometry.q (fun _ => 1) u := by
    have haQ' : C.bands.aQ x jstar (groupFreePart G u) ≤
        K * (goodAssignments.card : ℝ) := by
      simpa [K, goodAssignments] using haQ
    calc
      _ ≤ (K * (goodAssignments.card : ℝ)) *
            markWeight G C.bands.geometry.q (fun _ => 1) u :=
        mul_le_mul_of_nonneg_right haQ' hmarkNonneg
      _ = K * (goodAssignments.card : ℝ) *
            markWeight G C.bands.geometry.q (fun _ => 1) u := rfl
  have hweight : C.bands.weight x jstar u =
      C.bands.aQ x jstar (groupFreePart (C.bands.groups x) u) *
        markWeight (C.bands.groups x) C.bands.geometry.q (fun _ => 1) u := by
    simp [Erdos821.Blueprint.BandData.weight, hell]
  rw [hweight]
  change C.bands.aQ x jstar (groupFreePart G u) *
      markWeight G C.bands.geometry.q (fun _ => 1) u ≤ _
  calc
    C.bands.aQ x jstar (groupFreePart G u) *
        markWeight G C.bands.geometry.q (fun _ => 1) u ≤
      K * (goodAssignments.card : ℝ) *
        markWeight G C.bands.geometry.q (fun _ => 1) u := hAqmul
    _ = ∑ m ∈ goodAssignments,
          ∑ marks : MarkChoices G u,
            K * markBaseCoefficient G u *
              permissionEventSum (groupPrimeSet G \ markImage G u marks)
                C.bands.geometry.q u := hsumEq.symm
    _ = _ := by rfl

theorem aQ_le_micro_divisor_assignments
    (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar v : ℕ)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (hv : v ≠ 0) :
    C.bands.aQ x jstar v ≤
      listNormalizer C.bands x * (Fintype.card (MacroSlotIndex C)).factorial *
        ((Finset.univ.filter fun m : MicroAssignments C x jstar =>
          microAssignmentProduct C x jstar m ∣ v).card : ℝ) := by
  classical
  let fiber := Finset.univ.filter fun z : C.bands.Lists x jstar =>
    C.bands.listProduct z = v
  let divisorAssignments := Finset.univ.filter fun m : MicroAssignments C x jstar =>
    microAssignmentProduct C x jstar m ∣ v
  have hcard := listFiber_card_le_micro_divisor_count C x jstar hbound hj v hv
  have hcardR : (fiber.card : ℝ) ≤
      ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) * divisorAssignments.card := by
    exact_mod_cast hcard
  have hnorm : 0 ≤ listNormalizer C.bands x := by
    unfold listNormalizer
    exact inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  calc
    C.bands.aQ x jstar v = listNormalizer C.bands x * (fiber.card : ℝ) := by
      simp [fiber, Erdos821.Blueprint.BandData.aQ, listNormalizer]
    _ ≤ listNormalizer C.bands x *
          ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) * divisorAssignments.card := by
      calc
        listNormalizer C.bands x * (fiber.card : ℝ) ≤
            listNormalizer C.bands x *
              (((Fintype.card (MacroSlotIndex C)).factorial : ℝ) * divisorAssignments.card) :=
          mul_le_mul_of_nonneg_left hcardR hnorm
        _ = listNormalizer C.bands x *
              ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) * divisorAssignments.card := by ring



end

end Erdos821.P9Core
