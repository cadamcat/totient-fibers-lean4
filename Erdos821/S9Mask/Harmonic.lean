import Erdos821.Blueprint.Candidate

/-! Weighted Euler products and the multi-group marked harmonic sum `harmonicP`. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S9Mask
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Harmonic weight with a prime-dependent damping, once per distinct prime. -/
def wHarm (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (∏ p ∈ n.primeFactors, w p) / (n : ℝ)

theorem wHarm_nonneg (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) (n : ℕ) : 0 ≤ wHarm w n := by
  unfold wHarm
  split
  · exact le_rfl
  · exact div_nonneg (Finset.prod_nonneg fun p _ => hw p) (Nat.cast_nonneg _)

theorem wHarm_one (w : ℕ → ℝ) : wHarm w 1 = 1 := by simp [wHarm]

theorem wHarm_mul (w : ℕ → ℝ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    wHarm w (m * n) = wHarm w m * wHarm w n := by
  by_cases hm : m = 0
  · simp [hm, wHarm]
  by_cases hn : n = 0
  · simp [hn, wHarm]
  simp only [wHarm, hm, hn, mul_ne_zero hm hn, ite_false,
    hcop.primeFactors_mul, Finset.prod_union hcop.disjoint_primeFactors, Nat.cast_mul]
  ring

theorem wHarm_prime_succ (w : ℕ → ℝ) (p a : ℕ) (hp : p.Prime) :
    wHarm w (p ^ (a + 1)) = w p / (p : ℝ) ^ (a + 1) := by
  simp [wHarm, hp.ne_zero, Nat.primeFactors_prime_pow (by omega : a + 1 ≠ 0) hp]

theorem wHarm_prime_hasSum (w : ℕ → ℝ) (p : ℕ) (hp : p.Prime) :
    HasSum (fun a : ℕ => wHarm w (p ^ a)) (1 + w p / ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := (div_lt_one (by positivity)).mpr hp1
  have hf : 1 - 1 / (p : ℝ) ≠ 0 := by linarith
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hgeo := hasSum_geometric_of_lt_one hr0 hr1
  have htail : HasSum (fun a : ℕ => wHarm w (p ^ (a + 1))) (w p / ((p : ℝ) - 1)) := by
    convert hgeo.mul_left (w p / (p : ℝ)) using 1
    · ext a
      rw [wHarm_prime_succ w p a hp]
      simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
      ring
    · field_simp [hp0, hf, hpm]
  have hall : HasSum (fun a : ℕ => wHarm w (p ^ a))
      (wHarm w (p ^ 0) + w p / ((p : ℝ) - 1)) :=
    HasSum.zero_add (f := fun a : ℕ => wHarm w (p ^ a)) htail
  simpa [wHarm_one] using hall

/-- Finite Euler product for a nonnegative prime-dependent damping. -/
theorem wHarm_euler_hasSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w : ℕ → ℝ)
    (hw : ∀ p, 0 ≤ w p) :
    HasSum (fun n : Nat.factoredNumbers P => wHarm w n)
      (∏ p ∈ P, (1 + w p / ((p : ℝ) - 1))) := by
  have hnorm : ∀ {p : ℕ}, p.Prime → Summable (fun a : ℕ => ‖wHarm w (p ^ a)‖) := by
    intro p hp
    apply (wHarm_prime_hasSum w p hp).summable.congr
    intro a
    simp only [Real.norm_eq_abs, abs_of_nonneg (wHarm_nonneg w hw (p ^ a))]
  have hseries := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (wHarm_one w) (wHarm_mul w) hnorm P).2
  rw [Finset.filter_true_of_mem hP] at hseries
  convert hseries using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (wHarm_prime_hasSum w p (hP p hp)).tsum_eq.symm

/-- The same Euler product, as a sum over all natural numbers. -/
theorem wHarm_euler_hasSum_nat (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w : ℕ → ℝ)
    (hw : ∀ p, 0 ≤ w p) :
    HasSum (fun n : ℕ => if 0 < n ∧ n.primeFactors ⊆ P then wHarm w n else 0)
      (∏ p ∈ P, (1 + w p / ((p : ℝ) - 1))) := by
  classical
  have hsub := wHarm_euler_hasSum P hP w hw
  have hind := (hasSum_subtype_iff_indicator (s := Nat.factoredNumbers P)
    (f := wHarm w)).mp hsub
  apply hind.congr_fun
  intro n
  simp [Set.indicator, Nat.mem_factoredNumbers_iff_primeFactors_subset, Nat.pos_iff_ne_zero]

/-- Product over a set of primes of `q^|A| / ∏ A` times the reweighted Euler product. -/
theorem marked_value_eq (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P)
    (q : ℝ) (hq : 0 ≤ q) :
    q ^ A.card / ((∏ p ∈ A, p : ℕ) : ℝ) *
        ∏ p ∈ P, (1 + (if p ∈ A then 1 else q) / ((p : ℝ) - 1)) =
      (∏ p ∈ P, (1 + q / ((p : ℝ) - 1))) * ∏ p ∈ A, q / ((p : ℝ) - 1 + q) := by
  classical
  rw [← Finset.prod_sdiff hA, ← Finset.prod_sdiff hA (f := fun p : ℕ => 1 + q / ((p : ℝ) - 1))]
  have hout : (∏ p ∈ P \ A, (1 + (if p ∈ A then 1 else q) / ((p : ℝ) - 1))) =
      ∏ p ∈ P \ A, (1 + q / ((p : ℝ) - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    simp [(Finset.mem_sdiff.mp hp).2]
  have hconst : q ^ A.card / ((∏ p ∈ A, p : ℕ) : ℝ) = ∏ p ∈ A, q / (p : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_prod]
  have hin : (∏ p ∈ A, q / (p : ℝ)) *
      (∏ p ∈ A, (1 + (if p ∈ A then 1 else q) / ((p : ℝ) - 1))) =
      (∏ p ∈ A, (1 + q / ((p : ℝ) - 1))) * ∏ p ∈ A, q / ((p : ℝ) - 1 + q) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p (hA hp)).one_lt
    have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpq : (p : ℝ) - 1 + q ≠ 0 := by linarith
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    simp only [hp, ite_true]
    field_simp
    ring
  rw [hout, hconst]
  calc
    (∏ p ∈ A, q / (p : ℝ)) *
        ((∏ p ∈ P \ A, (1 + q / ((p : ℝ) - 1))) *
          ∏ p ∈ A, (1 + (if p ∈ A then 1 else q) / ((p : ℝ) - 1))) =
      (∏ p ∈ P \ A, (1 + q / ((p : ℝ) - 1))) *
        ((∏ p ∈ A, q / (p : ℝ)) *
          ∏ p ∈ A, (1 + (if p ∈ A then 1 else q) / ((p : ℝ) - 1))) := by ring
    _ = _ := by rw [hin]; ring

/-- Sum of the damped harmonic weight over the multiples of a set of marked primes. -/
theorem marked_hasSum (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P)
    (q : ℝ) (hq : 0 ≤ q) :
    HasSum (fun n : ℕ =>
        if 0 < n ∧ n.primeFactors ⊆ P ∧ (∀ p ∈ A, p ∣ n) then wHarm (fun _ => q) n else 0)
      ((∏ p ∈ P, (1 + q / ((p : ℝ) - 1))) * ∏ p ∈ A, q / ((p : ℝ) - 1 + q)) := by
  classical
  set M : ℕ := ∏ p ∈ A, p with hMdef
  have hAprime : ∀ p ∈ A, p.Prime := fun p hp => hP p (hA hp)
  have hM0 : 0 < M := Finset.prod_pos fun p hp => (hAprime p hp).pos
  have hMpf : M.primeFactors = A := Nat.primeFactors_prod hAprime
  have hdivM (n : ℕ) : (∀ p ∈ A, p ∣ n) ↔ M ∣ n := by
    constructor
    · intro h
      exact Finset.prod_primes_dvd n (fun p hp => (hAprime p hp).prime) h
    · intro h p hp
      exact dvd_trans (Finset.dvd_prod_of_mem _ hp) h
  let w : ℕ → ℝ := fun p => if p ∈ A then 1 else q
  have hw : ∀ p, 0 ≤ w p := by
    intro p
    dsimp [w]
    split
    · exact zero_le_one
    · exact hq
  have hbase := (wHarm_euler_hasSum_nat P hP w hw).mul_left (q ^ A.card / (M : ℝ))
  rw [marked_value_eq P A hP hA q hq] at hbase
  let f : ℕ → ℝ := fun n =>
    if 0 < n ∧ n.primeFactors ⊆ P ∧ (∀ p ∈ A, p ∣ n) then wHarm (fun _ => q) n else 0
  have hinj : Function.Injective (fun m : ℕ => M * m) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left hM0 h
  have hrange : ∀ n, n ∉ Set.range (fun m : ℕ => M * m) → f n = 0 := by
    intro n hn
    dsimp [f]
    rw [ite_eq_right_iff]
    rintro ⟨_, _, hdiv⟩
    exfalso
    obtain ⟨m, hm⟩ := (hdivM n).mp hdiv
    exact hn ⟨m, hm.symm⟩
  rw [← hinj.hasSum_iff hrange]
  convert hbase using 1
  ext m
  dsimp [f, Function.comp]
  by_cases hm : m = 0
  · simp [hm]
  have hMm0 : M * m ≠ 0 := mul_ne_zero hM0.ne' hm
  have hpfMm : (M * m).primeFactors = A ∪ m.primeFactors := by
    rw [Nat.primeFactors_mul hM0.ne' hm, hMpf]
  have hsubiff : (M * m).primeFactors ⊆ P ↔ m.primeFactors ⊆ P := by
    rw [hpfMm, Finset.union_subset_iff]
    exact ⟨fun h => h.2, fun h => ⟨hA, h⟩⟩
  have hdivMm : ∀ p ∈ A, p ∣ M * m := (hdivM (M * m)).mpr (dvd_mul_right M m)
  have hpos : 0 < M * m := Nat.pos_of_ne_zero hMm0
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  by_cases hsub : m.primeFactors ⊆ P
  · rw [if_pos ⟨hpos, hsubiff.mpr hsub, hdivMm⟩, if_pos ⟨hmpos, hsub⟩]
    simp only [wHarm, hMm0, hm, ite_false, hpfMm, Finset.prod_const, Nat.cast_mul]
    have hcard : (A ∪ m.primeFactors).card = A.card + (m.primeFactors \ A).card := by
      rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
    have hw' : (∏ p ∈ m.primeFactors, w p) = q ^ (m.primeFactors \ A).card := by
      dsimp [w]
      rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
      congr 2
      ext p
      simp [Finset.mem_sdiff]
    rw [hw', hcard, pow_add]
    have hM0' : (M : ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hm0' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp
  · rw [if_neg (fun h => hsub (hsubiff.mp h.2.1)), if_neg (fun h => hsub h.2), mul_zero]

end Erdos821.S9Mask
