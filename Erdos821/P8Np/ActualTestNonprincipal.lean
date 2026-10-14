import Erdos821.Blueprint.Proxy
import Erdos821.P5.Basic
import Erdos821.P8.MellinVariation
import Erdos821.P8.ProxySupport
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Np
open Blueprint Blueprint.Analytic

/-- The actual-test branch of proxy discrepancy. Enumerate rough integers by
nondecreasing prime lists and use Siegel--Walfisz on the last prime interval,
then partial summation for the Mellin weight. This statement includes all
characters modulo a logarithmically bounded modulus, including imprimitive
ones, and the saving exponent A is independent of the twist/modulus bound B. -/
def ActualTestNonprincipalTask : Prop :=
  ClassicalInputs → ∀ b kappa B A : ℝ,
    0 < b → 0 < kappa → kappa < 1 / 50 → 0 < B → 0 < A →
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (lo hi u : ℝ) (r : ℕ)
      (chi : DirichletCharacter ℂ r),
      TestAllowed b kappa I → x ^ (b / 4) ≤ lo → lo ≤ hi → hi ≤ x ^ (2 : ℕ) →
      1 ≤ r → (r : ℝ) ≤ L x ^ B → chi ≠ 1 → |u| ≤ L x ^ B →
      ‖∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
        (test I x n : ℂ) * chi (n : ZMod r) * mellin n u / (n : ℂ)‖ ≤ L x ^ (-A)

private noncomputable def characterWeight {r : ℕ} (chi : DirichletCharacter ℂ r)
    (u : ℝ) (n : ℕ) : ℂ :=
  chi (n : ZMod r) * mellin n u / (n : ℂ)

private def lastPrimeLower (y lo : ℝ) (m : ℕ) : ℕ :=
  max (⌊y⌋₊ + 1) (max ⌈lo / (m : ℝ)⌉₊ (Nat.maxPrimeFac m))

private def lastPrimeUpper (hi : ℝ) (m : ℕ) : ℕ := ⌊hi / (m : ℝ)⌋₊

private def lastPrimeSet (y lo hi : ℝ) (m : ℕ) : Finset ℕ :=
  if rough y m then
    (Finset.Icc (lastPrimeLower y lo m) (lastPrimeUpper hi m)).filter Nat.Prime
  else ∅

private lemma characterWeight_mul {r : ℕ} (chi : DirichletCharacter ℂ r)
    (u : ℝ) (m q : ℕ) (hm : 0 < m) (hq : 0 < q) :
    characterWeight chi u (m * q) = characterWeight chi u m * characterWeight chi u q := by
  unfold characterWeight
  simp only [map_mul, Nat.cast_mul,
    Erdos821.P5Core.mellin_mul (m : ℝ) (q : ℝ) u (by exact_mod_cast hm) (by exact_mod_cast hq)]
  ring

private lemma mem_nat_interval {lo hi : ℝ} (hhi : 0 ≤ hi) (n : ℕ) :
    n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ ↔ lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi := by
  simp only [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hhi]

/-- Split each rough integer at its greatest prime factor.  The q-fiber is an
interval of primes; in particular, the condition `q ≥ maxPrimeFac m` handles
repeated largest factors without a squarefree assumption. -/
private theorem rough_characterWeight_reindex {y lo hi u : ℝ} {r : ℕ}
    (chi : DirichletCharacter ℂ r) (hy : 0 ≤ y) (hlo : 1 < lo) (hhi : lo ≤ hi) :
    (∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough y), characterWeight chi u n) =
      ∑ m ∈ Finset.Icc 1 ⌊hi⌋₊,
        characterWeight chi u m * ∑ q ∈ lastPrimeSet y lo hi m, characterWeight chi u q := by
  classical
  let S := (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough y)
  let M := Finset.Icc 1 ⌊hi⌋₊
  let Q := lastPrimeSet y lo hi
  let T := M.biUnion fun m => (Q m).image fun q => (m, q)
  have hhi0 : 0 ≤ hi := le_trans (by linarith) hhi
  let hmapData : ∀ n, n ∈ S → Σ m : ℕ, {q : ℕ // q ∈ Q m} := fun n hn => by
    let q := Nat.maxPrimeFac n
    let m := n / q
    have hnI : n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := (Finset.mem_filter.mp hn).1
    have hnR : rough y n := (Finset.mem_filter.mp hn).2
    have hnr : (1 : ℝ) < (n : ℝ) :=
      lt_of_lt_of_le hlo ((mem_nat_interval hhi0 n).mp hnI).1
    have hn1 : 1 < n := by exact_mod_cast hnr
    have hqP : q.Prime := Nat.prime_maxPrimeFac_of_one_lt hn1
    have hqd : q ∣ n := Nat.maxPrimeFac_dvd
    have hqle : q ≤ n := Nat.le_of_dvd (by omega) hqd
    have hmpos : 0 < m := Nat.div_pos hqle hqP.pos
    have hmprod : m * q = n := Nat.div_mul_cancel hqd
    have hmrough : rough y m := by
      refine ⟨hmpos, ?_⟩
      intro p hp hpm
      have hmn : m ∣ n := by
        rw [← hmprod]
        exact dvd_mul_of_dvd_left (dvd_refl m) q
      exact hnR.2 p hp (dvd_trans hpm hmn)
    have hqgt : y < (q : ℝ) := hnR.2 q hqP hqd
    have hqcut : ⌊y⌋₊ + 1 ≤ q := by
      by_contra h
      have hqfloor : q ≤ ⌊y⌋₊ := by omega
      have hqleR : (q : ℝ) ≤ y := (show (q : ℝ) ≤ (⌊y⌋₊ : ℝ) by exact_mod_cast hqfloor).trans (Nat.floor_le hy)
      exact (not_lt_of_ge hqleR) hqgt
    have hmax : Nat.maxPrimeFac m ≤ q := by
      have heq : q = max (Nat.maxPrimeFac m) q := by
        calc
          q = Nat.maxPrimeFac n := rfl
          _ = Nat.maxPrimeFac (m * q) := by rw [hmprod]
          _ = max (Nat.maxPrimeFac m) (Nat.maxPrimeFac q) :=
            Nat.maxPrimeFac_mul (by omega) hqP.ne_zero
          _ = max (Nat.maxPrimeFac m) q := by rw [hqP.maxPrimeFac_eq_self]
      exact max_eq_right_iff.mp heq.symm
    have hdivlo : lo / (m : ℝ) ≤ (q : ℝ) := by
      apply (div_le_iff₀ (by exact_mod_cast hmpos)).2
      have hncast : (n : ℝ) = (m : ℝ) * (q : ℝ) := by
        exact_mod_cast hmprod.symm
      simpa [hncast, mul_comm] using (mem_nat_interval hhi0 n |>.mp hnI).1
    have hqlo : ⌈lo / (m : ℝ)⌉₊ ≤ q := Nat.ceil_le.mpr hdivlo
    have hdivhi : (q : ℝ) ≤ hi / (m : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hmpos)).2
      have hncast : (n : ℝ) = (m : ℝ) * (q : ℝ) := by
        exact_mod_cast hmprod.symm
      simpa [hncast, mul_comm] using (mem_nat_interval hhi0 n |>.mp hnI).2
    have hqhi : q ≤ ⌊hi / (m : ℝ)⌋₊ := Nat.le_floor hdivhi
    have hqmem : q ∈ Q m := by
      change q ∈ if rough y m then
        (Finset.Icc (lastPrimeLower y lo m) (lastPrimeUpper hi m)).filter Nat.Prime else ∅
      rw [if_pos hmrough]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨
          max_le hqcut (max_le hqlo hmax), hqhi⟩, hqP⟩
    exact ⟨m, ⟨q, hqmem⟩⟩
  let hmap : ∀ n, n ∈ S → ℕ × ℕ := fun n _ =>
    (n / Nat.maxPrimeFac n, Nat.maxPrimeFac n)
  have hmap_mem (n : ℕ) (hn : n ∈ S) : hmap n hn ∈ T := by
    let q := Nat.maxPrimeFac n
    let m := n / q
    have hnI := (Finset.mem_filter.mp hn).1
    have hnr : 1 < n := by
      have hreal := (mem_nat_interval hhi0 n).mp hnI
      exact_mod_cast (lt_of_lt_of_le hlo hreal.1)
    have hqP := Nat.prime_maxPrimeFac_of_one_lt hnr
    have hqd : Nat.maxPrimeFac n ∣ n := Nat.maxPrimeFac_dvd
    have hqle : Nat.maxPrimeFac n ≤ n := Nat.le_of_dvd (by omega) hqd
    have hmpos : 0 < n / Nat.maxPrimeFac n := Nat.div_pos hqle hqP.pos
    have hmprod : (n / Nat.maxPrimeFac n) * Nat.maxPrimeFac n = n := Nat.div_mul_cancel hqd
    have hmle : m ≤ n := by
      calc
        m ≤ m * q := Nat.le_mul_of_pos_right _ hqP.pos
        _ = n := hmprod
    have hreal := (mem_nat_interval hhi0 n).mp hnI
    have hmleR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmle
    have hmhiR : (m : ℝ) ≤ hi := hmleR.trans hreal.2
    have hmhi : m ≤ ⌊hi⌋₊ := Nat.le_floor hmhiR
    have hmM : m ∈ M := Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hmpos.ne', hmhi⟩
    have hqmem : q ∈ Q m := (hmapData n hn).2.property
    change (m, q) ∈ T
    exact Finset.mem_biUnion.mpr ⟨m, hmM, Finset.mem_image.mpr ⟨q, hqmem, rfl⟩⟩
  have hmap_inj : ∀ n₁ hn₁ n₂ hn₂, hmap n₁ hn₁ = hmap n₂ hn₂ → n₁ = n₂ := by
    intro n₁ hn₁ n₂ hn₂ heq
    have hprod₁ : (n₁ / Nat.maxPrimeFac n₁) * Nat.maxPrimeFac n₁ = n₁ := by
      exact Nat.div_mul_cancel Nat.maxPrimeFac_dvd
    have hprod₂ : (n₂ / Nat.maxPrimeFac n₂) * Nat.maxPrimeFac n₂ = n₂ := by
      exact Nat.div_mul_cancel Nat.maxPrimeFac_dvd
    have hm : n₁ / Nat.maxPrimeFac n₁ = n₂ / Nat.maxPrimeFac n₂ := by
      simpa [hmap] using congrArg Prod.fst heq
    have hqval : Nat.maxPrimeFac n₁ = Nat.maxPrimeFac n₂ := by
      simpa [hmap] using congrArg Prod.snd heq
    rw [← hprod₁, ← hprod₂, hm, hqval]
  have hmap_surj (z : ℕ × ℕ) (hz : z ∈ T) :
      ∃ n hn, hmap n hn = z := by
    rcases z with ⟨m, q⟩
    simp only [T, Finset.mem_biUnion] at hz
    rcases hz with ⟨m', hmM, hz⟩
    rcases Finset.mem_image.mp hz with ⟨q', hqmem, hmq⟩
    have hmEq : m' = m := congrArg Prod.fst hmq
    have hqEq : q' = q := congrArg Prod.snd hmq
    subst m'
    subst q'
    have hmR : rough y m := by
      by_contra h
      simp [Q, lastPrimeSet, h] at hqmem
    have hqmem' : q ∈ (Finset.Icc (lastPrimeLower y lo m) (lastPrimeUpper hi m)).filter Nat.Prime := by
      simpa [Q, lastPrimeSet, hmR] using hqmem
    have hI := (Finset.mem_filter.mp hqmem').1
    have hIcc : max (⌊y⌋₊ + 1) (max ⌈lo / (m : ℝ)⌉₊ (Nat.maxPrimeFac m)) ≤ q ∧
        q ≤ ⌊hi / (m : ℝ)⌋₊ := by
      simpa [lastPrimeLower, lastPrimeUpper] using Finset.mem_Icc.mp hI
    have hLow : max (⌊y⌋₊ + 1) (max ⌈lo / (m : ℝ)⌉₊ (Nat.maxPrimeFac m)) ≤ q := hIcc.1
    have hUp : q ≤ ⌊hi / (m : ℝ)⌋₊ := hIcc.2
    have hqP : q.Prime := (Finset.mem_filter.mp hqmem').2
    have hmpos : 0 < m := hmR.1
    have hqlo : ⌊y⌋₊ + 1 ≤ q := by
      exact le_trans (Nat.le_max_left _ _) hLow
    have hqgt : y < (q : ℝ) := by
      calc y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
        _ = (⌊y⌋₊ + 1 : ℕ) := by norm_cast
        _ ≤ (q : ℝ) := by exact_mod_cast hqlo
    have hnrough : rough y (m * q) := by
      refine ⟨Nat.mul_pos hmpos hqP.pos, ?_⟩
      intro p hp hpd
      rcases (Nat.Prime.dvd_mul hp).mp hpd with hpm | hpq
      · exact hmR.2 p hp hpm
      · have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqP).mp hpq
        simpa [heq] using hqgt
    have hqmax : Nat.maxPrimeFac (m * q) = q := by
      have hmax : Nat.maxPrimeFac m ≤ q := by
        calc
          Nat.maxPrimeFac m ≤ max ⌈lo / (m : ℝ)⌉₊ (Nat.maxPrimeFac m) := Nat.le_max_right _ _
          _ ≤ max (⌊y⌋₊ + 1) (max ⌈lo / (m : ℝ)⌉₊ (Nat.maxPrimeFac m)) := Nat.le_max_right _ _
          _ ≤ q := hLow
      simp [Nat.maxPrimeFac_mul hmpos.ne' hqP.ne_zero, hqP.maxPrimeFac_eq_self, hmax]
    have hloq : ⌈lo / (m : ℝ)⌉₊ ≤ q := by
      calc
        ⌈lo / (m : ℝ)⌉₊ ≤ max ⌈lo / (m : ℝ)⌉₊ (Nat.maxPrimeFac m) := Nat.le_max_left _ _
        _ ≤ max (⌊y⌋₊ + 1) (max ⌈lo / (m : ℝ)⌉₊ (Nat.maxPrimeFac m)) := Nat.le_max_right _ _
        _ ≤ q := hLow
    have hhiq : q ≤ ⌊hi / (m : ℝ)⌋₊ := by
      exact hUp
    have hqloR : lo / (m : ℝ) ≤ (q : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hloq)
    have hqhiR : (q : ℝ) ≤ hi / (m : ℝ) := by
      have hqfloor : (q : ℝ) ≤ (⌊hi / (m : ℝ)⌋₊ : ℝ) := by exact_mod_cast hhiq
      exact hqfloor.trans (Nat.floor_le (show (0 : ℝ) ≤ hi / (m : ℝ) by positivity))
    have hnlo : lo ≤ ((m * q : ℕ) : ℝ) := by
      simpa [Nat.cast_mul, mul_comm] using (div_le_iff₀ (by exact_mod_cast hmpos)).mp hqloR
    have hnhi : ((m * q : ℕ) : ℝ) ≤ hi := by
      simpa [Nat.cast_mul, mul_comm] using (le_div_iff₀ (by exact_mod_cast hmpos)).mp hqhiR
    have hnI : m * q ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := (mem_nat_interval hhi0 _).mpr ⟨hnlo, hnhi⟩
    have hnS : m * q ∈ S := Finset.mem_filter.mpr ⟨hnI, hnrough⟩
    refine ⟨m * q, hnS, ?_⟩
    change ((m * q) / Nat.maxPrimeFac (m * q), Nat.maxPrimeFac (m * q)) = (m, q)
    rw [hqmax]
    apply Prod.ext
    · simpa [Nat.mul_comm] using Nat.mul_div_right m hqP.pos
    · rfl
  calc
    _ = ∑ z ∈ T, characterWeight chi u z.1 * characterWeight chi u z.2 := by
      apply Finset.sum_bij (fun n hn => hmap n hn)
      · exact hmap_mem
      · exact hmap_inj
      · exact hmap_surj
      · intro n hn
        let q := Nat.maxPrimeFac n
        let m := n / q
        have hnR : rough y n := (Finset.mem_filter.mp hn).2
        have hnr : 1 < n := by
          have hnI := (Finset.mem_filter.mp hn).1
          exact_mod_cast (lt_of_lt_of_le hlo ((mem_nat_interval hhi0 n).mp hnI).1)
        have hqP : q.Prime := Nat.prime_maxPrimeFac_of_one_lt hnr
        have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) Nat.maxPrimeFac_dvd) hqP.pos
        have hqpos : 0 < q := hqP.pos
        have hprod : m * q = n := Nat.div_mul_cancel Nat.maxPrimeFac_dvd
        change characterWeight chi u n = characterWeight chi u m * characterWeight chi u q
        rw [← hprod, characterWeight_mul chi u m q hmpos hqpos]
    _ = ∑ m ∈ M, characterWeight chi u m * ∑ q ∈ Q m, characterWeight chi u q := by
      have hdisj : Set.PairwiseDisjoint (↑M) (fun m => (Q m).image fun q => (m, q)) := by
        intro m hm n hn hmn
        apply Finset.disjoint_left.mpr
        intro z hz hz'
        obtain ⟨q₁, hq₁, hz₁⟩ := Finset.mem_image.mp hz
        obtain ⟨q₂, hq₂, hz₂⟩ := Finset.mem_image.mp hz'
        apply hmn
        exact congrArg Prod.fst (hz₁.trans hz₂.symm)
      rw [Finset.sum_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro m hm
      have hinj : Set.InjOn (fun q : ℕ => (m, q)) (Q m) := by
        intro q₁ hq₁ q₂ hq₂ heq
        exact congrArg Prod.snd heq
      rw [Finset.sum_image hinj]
      simp only [Prod.fst, Prod.snd]
      rw [← Finset.mul_sum]

private lemma norm_characterWeight_le {r : ℕ} (chi : DirichletCharacter ℂ r)
    (u : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖characterWeight chi u n‖ ≤ (n : ℝ)⁻¹ := by
  have hweight : characterWeight chi u n =
      chi (n : ZMod r) * (mellin n u / (n : ℂ)) := by
    simp only [characterWeight]
    rw [mul_div_assoc]
  rw [hweight, norm_mul]
  have hmellin : ‖mellin n u / (n : ℂ)‖ = (n : ℝ)⁻¹ := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hm := Erdos821.P8Core.norm_mellinWeight hnR u
    unfold Erdos821.P8Core.mellinWeight at hm
    have hcast : ((n : ℝ) : ℂ) = (n : ℂ) := by norm_cast
    rw [hcast] at hm
    exact hm
  rw [hmellin]
  calc
    ‖chi (n : ZMod r)‖ * (n : ℝ)⁻¹ ≤ 1 * (n : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (chi.norm_le_one _) (by positivity)
    _ = _ := by ring

private lemma reciprocal_sum_floor_le (y : ℝ) (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℝ)⁻¹) ≤ 1 + Real.log y := by
  simpa [harmonic_eq_sum_Icc] using harmonic_floor_le_one_add_log y hy

private lemma eventually_log_absorb (A K : ℝ) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, K * L x ^ (-(A + 2)) * (1 + 2 * L x) ≤ L x ^ (-A) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max (1 : ℝ) (3 * K)))] with x hx
  have hL : 1 ≤ L x := le_trans (le_max_left _ _) hx
  have hKx : 3 * K ≤ L x := le_trans (le_max_right _ _) hx
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL
  have hfac : 1 + 2 * L x ≤ 3 * L x := by linarith
  have hcoeff : 0 ≤ K * L x ^ (-(A + 2)) := by positivity
  calc
    K * L x ^ (-(A + 2)) * (1 + 2 * L x) ≤
        K * L x ^ (-(A + 2)) * (3 * L x) :=
          mul_le_mul_of_nonneg_left hfac hcoeff
    _ = 3 * K * (L x ^ (-(A + 2)) * L x) := by ring
    _ = 3 * K * L x ^ (-(A + 1)) := by
      congr 1
      calc
        L x ^ (-(A + 2)) * L x = L x ^ (-(A + 2)) * L x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = L x ^ (-(A + 2) + 1) := by rw [← Real.rpow_add hLpos]
        _ = L x ^ (-(A + 1)) := by congr 1 <;> ring
    _ ≤ L x * L x ^ (-(A + 1)) :=
      mul_le_mul_of_nonneg_right hKx (Real.rpow_nonneg (by linarith [hL]) _)
    _ = L x ^ (-A) := by
      calc
        L x * L x ^ (-(A + 1)) = L x ^ (1 : ℝ) * L x ^ (-(A + 1)) := by rw [Real.rpow_one]
        _ = L x ^ (1 + (-(A + 1))) := by rw [← Real.rpow_add hLpos]
        _ = L x ^ (-A) := by rw [show 1 + (-(A + 1)) = -A by ring]

theorem ActualTestNonprincipalTask_proof : ActualTestNonprincipalTask := by
  intro hc b kappa B A hb hkappa hklt hB hA
  have hE : 0 < A + 2 := by linarith
  obtain ⟨K, hK, hharm⟩ := hc.harmonic (1 / 2) 2 B (A + 2)
    (by norm_num) (by norm_num) hB hE
  have hWprime := Erdos821.P8Core.eventually_W_le_rpow_exponent_ge (b / 4) (by positivity)
  have hWrough := Erdos821.P8Core.eventually_W_le_rpow_exponent_ge b hb
  filter_upwards [hharm, hWprime, hWrough, eventually_gt_atTop (1 : ℝ),
    eventually_log_absorb A K hK] with x hharmx hWprimeX hWroughX hx hAbsorb
  intro I lo hi u r chi hallowed hlo horder hhi hr hmod hchi hu
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := Real.log_pos hx
  have hWeq : Real.exp (L x ^ (1 / 2 : ℝ)) = W x := by
    simp [W, Real.sqrt_eq_rpow]
  have hrecip :
      (∑ m ∈ Finset.Icc 1 ⌊hi⌋₊, (m : ℝ)⁻¹) ≤ 1 + 2 * L x := by
    have hhi1 : 1 ≤ hi := by
      have hexp : 1 < x ^ (b / 4) := Real.one_lt_rpow hx (by positivity)
      exact le_trans hexp.le (hlo.trans horder)
    calc
      _ ≤ 1 + Real.log hi := reciprocal_sum_floor_le hi hhi1
      _ ≤ 1 + Real.log (x ^ (2 : ℕ)) := by gcongr
      _ = 1 + 2 * L x := by simp only [L, Real.log_pow, Nat.cast_ofNat]
  cases I with
  | prime =>
      have hWlo : Real.exp (L x ^ (1 / 2 : ℝ)) ≤ lo := by
        calc
          Real.exp (L x ^ (1 / 2 : ℝ)) = W x := hWeq
          _ ≤ x ^ (b / 4) := hWprimeX (b / 4) le_rfl
          _ ≤ lo := hlo
      have hprimeSum :
          (∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
            (test .prime x n : ℂ) * chi (n : ZMod r) * mellin n u / (n : ℂ)) =
          ∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter Nat.Prime, characterWeight chi u n := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hp : n.Prime <;> simp [test, characterWeight, hp]
      rw [hprimeSum]
      have hhi' : hi ≤ x ^ (2 : ℝ) := by
        change hi ≤ x ^ ((2 : ℕ) : ℝ)
        rw [Real.rpow_natCast]
        exact hhi
      have hbound := hharmx lo hi u r chi hWlo horder hhi' hr hmod hchi hu
      have hbound' : ‖∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter Nat.Prime,
          characterWeight chi u n‖ ≤ K * L x ^ (-(A + 2)) := by
        simpa [characterWeight] using hbound
      have htrivial : K * L x ^ (-(A + 2)) ≤
          K * L x ^ (-(A + 2)) * (1 + 2 * L x) := by
        calc
          K * L x ^ (-(A + 2)) = K * L x ^ (-(A + 2)) * 1 := by ring
          _ ≤ K * L x ^ (-(A + 2)) * (1 + 2 * L x) :=
            mul_le_mul_of_nonneg_left (by linarith [Real.log_pos hx]) (by positivity)
      exact hbound'.trans (htrivial.trans hAbsorb)
  | rough gamma =>
      change b ≤ gamma ∧ gamma ≤ 1 / 2 - kappa at hallowed
      have hyW : W x ≤ x ^ gamma := hWroughX gamma hallowed.1
      let y := x ^ gamma
      have hlo1 : 1 < lo := (Real.one_lt_rpow hx (by positivity)).trans_le hlo
      have hroughSum :
          (∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
            (test (.rough gamma) x n : ℂ) * chi (n : ZMod r) * mellin n u / (n : ℂ)) =
          ∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough y), characterWeight chi u n := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hrn : rough y n <;> simp [test, y, characterWeight, hrn]
      rw [hroughSum, rough_characterWeight_reindex chi (by positivity) hlo1 horder]
      have hinner (m : ℕ) (hm : m ∈ Finset.Icc 1 ⌊hi⌋₊) :
          ‖∑ q ∈ lastPrimeSet y lo hi m, characterWeight chi u q‖ ≤
            K * L x ^ (-(A + 2)) := by
        by_cases hmR : rough y m
        · have hQ : lastPrimeSet y lo hi m =
              (Finset.Icc (lastPrimeLower y lo m) (lastPrimeUpper hi m)).filter Nat.Prime := by
            simp [lastPrimeSet, hmR]
          rw [hQ]
          by_cases hle : lastPrimeLower y lo m ≤ lastPrimeUpper hi m
          · have hcut : y < (lastPrimeLower y lo m : ℝ) := by
              have hfloorlt : y < ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by
                simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one y
              have hfloorle : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤
                  (lastPrimeLower y lo m : ℝ) := by
                exact_mod_cast (Nat.le_max_left (⌊y⌋₊ + 1)
                  (max ⌈lo / (m : ℝ)⌉₊ (Nat.maxPrimeFac m)))
              exact hfloorlt.trans_le hfloorle
            have hWcut : W x ≤ (lastPrimeLower y lo m : ℝ) :=
              hyW.trans (hcut.le)
            have hlow : Real.exp (L x ^ (1 / 2 : ℝ)) ≤ (lastPrimeLower y lo m : ℝ) := by
              rw [hWeq]
              exact hWcut
            have hmone : 1 ≤ m := (Finset.mem_Icc.mp hm).1
            have hmreal : 1 ≤ (m : ℝ) := by exact_mod_cast hmone
            have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hmreal
            have hdivle : hi / (m : ℝ) ≤ hi := by
              apply (div_le_iff₀ hmpos).2
              calc
                hi = hi * 1 := by ring
                _ ≤ hi * (m : ℝ) := mul_le_mul_of_nonneg_left hmreal (by linarith [horder, hlo])
            have hhi0 : 0 ≤ hi := by linarith [horder, hlo1]
            have hdivnonneg : 0 ≤ hi / (m : ℝ) := div_nonneg hhi0 hmpos.le
            have hupper : (lastPrimeUpper hi m : ℝ) ≤ x ^ (2 : ℕ) := by
              calc
                (lastPrimeUpper hi m : ℝ) ≤ hi / (m : ℝ) :=
                  Nat.floor_le hdivnonneg
                _ ≤ hi := hdivle
                _ ≤ x ^ (2 : ℕ) := hhi
            have hupper' : (lastPrimeUpper hi m : ℝ) ≤ x ^ (2 : ℝ) := by
              change (lastPrimeUpper hi m : ℝ) ≤ x ^ ((2 : ℕ) : ℝ)
              rw [Real.rpow_natCast]
              exact hupper
            have horder' : (lastPrimeLower y lo m : ℝ) ≤
                (lastPrimeUpper hi m : ℝ) := by exact_mod_cast hle
            have hbound := hharmx (lastPrimeLower y lo m : ℝ)
              (lastPrimeUpper hi m : ℝ) u r chi hlow horder' hupper' hr hmod hchi hu
            simpa [characterWeight, Nat.ceil_natCast, Nat.floor_natCast] using hbound
          · have hzero : (∑ q ∈ (Finset.Icc (lastPrimeLower y lo m)
                (lastPrimeUpper hi m)).filter Nat.Prime, characterWeight chi u q) = 0 := by
              apply Finset.sum_eq_zero
              intro q hq
              have hqI : q ∈ Finset.Icc (lastPrimeLower y lo m) (lastPrimeUpper hi m) :=
                (Finset.mem_filter.mp hq).1
              exact (hle ((Finset.mem_Icc.mp hqI).1.trans (Finset.mem_Icc.mp hqI).2)).elim
            rw [hzero]
            simp
            exact mul_nonneg hK.le (Real.rpow_nonneg hLpos.le _)
        · simp [lastPrimeSet, hmR]
          exact mul_nonneg hK.le (Real.rpow_nonneg hLpos.le _)
      calc
        ‖∑ m ∈ Finset.Icc 1 ⌊hi⌋₊,
            characterWeight chi u m * ∑ q ∈ lastPrimeSet y lo hi m,
              characterWeight chi u q‖ ≤
            ∑ m ∈ Finset.Icc 1 ⌊hi⌋₊,
              ‖characterWeight chi u m * ∑ q ∈ lastPrimeSet y lo hi m,
                characterWeight chi u q‖ := norm_sum_le _ _
        _ = ∑ m ∈ Finset.Icc 1 ⌊hi⌋₊,
              ‖characterWeight chi u m‖ *
                ‖∑ q ∈ lastPrimeSet y lo hi m, characterWeight chi u q‖ := by simp [norm_mul]
        _ ≤ ∑ m ∈ Finset.Icc 1 ⌊hi⌋₊,
              (m : ℝ)⁻¹ * (K * L x ^ (-(A + 2))) := by
          apply Finset.sum_le_sum
          intro m hm
          have hmpos : 0 < m := by
            have hmone := (Finset.mem_Icc.mp hm).1
            omega
          exact mul_le_mul (norm_characterWeight_le chi u hmpos) (hinner m hm)
            (norm_nonneg _) (by positivity)
        _ = K * L x ^ (-(A + 2)) *
              ∑ m ∈ Finset.Icc 1 ⌊hi⌋₊, (m : ℝ)⁻¹ := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ K * L x ^ (-(A + 2)) * (1 + 2 * L x) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ ≤ L x ^ (-A) := hAbsorb


end P8Np
