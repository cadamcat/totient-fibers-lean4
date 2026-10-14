import Erdos821.S10.Tasks

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S10Cover
open Erdos821.Blueprint Erdos821.P10 Erdos821.P7Core
attribute [local instance] Classical.propDecidable

def candidateRange (x : ℝ) : Finset ℕ := Finset.Icc 1 ⌊2 * x⌋₊

def meshSlice (x b κ : ℝ) (N i : ℕ) : Finset (ℕ × ℕ) :=
  ((candidateRange x ×ˢ
      primeExponentBin (densityMeshPoint b κ N i)
        (densityMeshPoint b κ N (i + 1)) x).filter
        (fun z => z.2 ∣ 2 * z.1 + 1))

noncomputable def meshIndexSet (x b κ : ℝ) (N : ℕ) : Finset (Σ i : ℕ, ℕ × ℕ) :=
  (Finset.range N).sigma (fun i => meshSlice x b κ N i)

noncomputable def meshPointWeight (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N : ℕ) (z : Σ i : ℕ, ℕ × ℕ) : ℝ :=
  C.weighted x jstar z.2.1 *
    test (.rough (densityMeshPoint b κ N z.1)) x
      ((2 * z.2.1 + 1) / z.2.2)

def meshContribution (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N u : ℕ) : ℝ :=
  ∑ z ∈ meshIndexSet x b κ N,
    if z.2.1 = u then meshPointWeight C x jstar b κ N z else 0

theorem unbalancedMeshMass_eq_sigma (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N : ℕ) :
    unbalancedMeshMass C x jstar b κ N =
      ∑ z ∈ meshIndexSet x b κ N, meshPointWeight C x jstar b κ N z := by
  simp [unbalancedMeshMass, meshIndexSet, meshSlice, candidateRange,
    meshPointWeight, Finset.sum_sigma']

theorem sum_meshContribution_eq (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N : ℕ) :
    (∑ u ∈ candidateRange x, meshContribution C x jstar b κ N u) =
      unbalancedMeshMass C x jstar b κ N := by
  rw [unbalancedMeshMass_eq_sigma]
  unfold meshContribution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hzSigma := Finset.mem_sigma.mp hz
  have hzu : z.2.1 ∈ candidateRange x := by
    rcases hzSigma with ⟨hi, hslice⟩
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hslice).1).1
  simp [hzu]

lemma primeExponentBin_mem_of_bounds {x γ γ' : ℝ} {p : ℕ}
    (hx : 3 ≤ x) (hγ' : γ' ≤ 1) (hp : Nat.Prime p)
    (hlo : x ^ γ < (p : ℝ)) (hhi : (p : ℝ) ≤ x ^ γ') :
    p ∈ primeExponentBin γ γ' x := by
  have hxpos : 0 < x := by linarith
  have hcut := Classical.choose_spec (exists_logarithmic_dyadic_cutoff x hx)
  have hpow : x ^ γ' ≤ x := by
    have hpow' : x ^ γ' ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (x := x) (y := γ') (z := 1)
        (by linarith : (1 : ℝ) ≤ x) hγ'
    simpa using hpow'
  have hpCut : (p : ℝ) < ((2 ^ Classical.choose
      (exists_logarithmic_dyadic_cutoff x hx) : ℕ) : ℝ) := by
    have hxle : x ≤ 5 * x := by nlinarith
    linarith
  have hpCutNat : p < 2 ^ Classical.choose
      (exists_logarithmic_dyadic_cutoff x hx) := by exact_mod_cast hpCut
  simp only [primeExponentBin, dif_pos hx, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨hp.one_le, hpCutNat⟩, hp, hlo, hhi⟩

lemma exists_densityMeshBin {x b κ : ℝ} {N p : ℕ}
    (hx : 3 ≤ x) (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50)
    (hbκ : b < κ) (hN : 0 < N) (hp : Nat.Prime p)
    (hpLower : x ^ b < (p : ℝ))
    (hpUpper : (p : ℝ) ≤ x ^ ((1 / 2 : ℝ) - κ)) :
    ∃ i ∈ Finset.range N,
      p ∈ primeExponentBin (densityMeshPoint b κ N i)
        (densityMeshPoint b κ N (i + 1)) x := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hxone
  have htop : 0 < (1 / 2 : ℝ) - κ := by linarith
  have hwidth : 0 < (1 / 2 : ℝ) - κ - b := by linarith
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogLo := Real.log_lt_log (Real.rpow_pos_of_pos hxpos b) hpLower
  have hlogHi := Real.log_le_log hpPos hpUpper
  rw [Real.log_rpow hxpos b] at hlogLo
  rw [Real.log_rpow hxpos ((1 / 2 : ℝ) - κ)] at hlogHi
  have hαlo : b < Real.log (p : ℝ) / Real.log x :=
    (lt_div_iff₀ hlogx).2 (by simpa [mul_comm] using hlogLo)
  have hαhi : Real.log (p : ℝ) / Real.log x ≤ (1 / 2 : ℝ) - κ :=
    (div_le_iff₀ hlogx).2 (by simpa [mul_comm] using hlogHi)
  let step := ((1 / 2 : ℝ) - κ - b) / (N : ℝ)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hstep : 0 < step := div_pos hwidth hNreal
  let t := (Real.log (p : ℝ) / Real.log x - b) / step
  have htpos : 0 < t := by
    dsimp [t]
    exact div_pos (sub_pos.mpr hαlo) hstep
  have hwidthEq : (N : ℝ) * step = (1 / 2 : ℝ) - κ - b := by
    dsimp [step]
    field_simp
  have htle : t ≤ N := by
    apply (div_le_iff₀ hstep).2
    dsimp [t] at *
    rw [hwidthEq]
    linarith
  let i : ℕ := ⌈t⌉₊ - 1
  have hceilpos : 1 ≤ ⌈t⌉₊ := Nat.one_le_ceil_iff.mpr htpos
  have hceille : ⌈t⌉₊ ≤ N := Nat.ceil_le.mpr htle
  have hiadd : i + 1 = ⌈t⌉₊ := by
    dsimp [i]
    omega
  have hirange : i < N := by
    omega
  have hitlo : (i : ℝ) < t := by
    have hceillt : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one (le_of_lt htpos)
    rw [← hiadd] at hceillt
    exact (add_lt_add_iff_right (1 : ℝ)).mp (by
      simpa [Nat.cast_add] using hceillt)
  have hithi : t ≤ (i + 1 : ℝ) := by
    have hceil : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have hcast : (⌈t⌉₊ : ℝ) = (i : ℝ) + 1 := by
      rw [← hiadd]
      simp
    rw [hcast] at hceil
    exact hceil
  have hmeshLo : densityMeshPoint b κ N i < Real.log (p : ℝ) / Real.log x := by
    change (i : ℝ) < (Real.log (p : ℝ) / Real.log x - b) / step at hitlo
    have hmul := (lt_div_iff₀ hstep).1 hitlo
    have hpoint : (densityMeshPoint b κ N i) = b + step * (i : ℝ) := by
      dsimp [densityMeshPoint, step]
      field_simp
      <;> ring
    rw [hpoint]
    linarith
  have hmeshHi : Real.log (p : ℝ) / Real.log x ≤
      densityMeshPoint b κ N (i + 1) := by
    change (Real.log (p : ℝ) / Real.log x - b) / step ≤
      (i : ℝ) + 1 at hithi
    have hmul := (div_le_iff₀ hstep).1 hithi
    have hmul' : Real.log (p : ℝ) / Real.log x - b ≤
        ((i + 1 : ℕ) : ℝ) * step := by
      simpa [Nat.cast_add] using hmul
    have hpoint : densityMeshPoint b κ N (i + 1) =
        b + step * ((i + 1 : ℕ) : ℝ) := by
      dsimp [densityMeshPoint, step]
      field_simp
      <;> ring
    calc
      Real.log (p : ℝ) / Real.log x =
          b + (Real.log (p : ℝ) / Real.log x - b) := by ring
      _ ≤ b + ((i + 1 : ℕ) : ℝ) * step := by
        have hsum := add_le_add_left hmul' b
        nlinarith
      _ = densityMeshPoint b κ N (i + 1) := by rw [hpoint]; ring
  have hprimeLower : x ^ densityMeshPoint b κ N i < (p : ℝ) := by
    rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hxpos _ ) hpPos,
      Real.log_rpow hxpos]
    exact (lt_div_iff₀ hlogx).1 hmeshLo
  have hprimeUpper : (p : ℝ) ≤ x ^ densityMeshPoint b κ N (i + 1) := by
    rw [← Real.log_le_log_iff hpPos (Real.rpow_pos_of_pos hxpos _),
      Real.log_rpow hxpos]
    exact (div_le_iff₀ hlogx).1 hmeshHi
  refine ⟨i, Finset.mem_range.mpr hirange, ?_⟩
  have hγ'le : densityMeshPoint b κ N (i + 1) ≤ 1 := by
    have hiLe : i + 1 ≤ N := by omega
    have hiLeR : ((i + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hiLe
    have hfrac : ((i + 1 : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hNreal]
      nlinarith [hiLeR]
    have hcoef : 0 ≤ (1 / 2 : ℝ) - κ - b := by linarith
    have hmul := mul_le_mul_of_nonneg_left hfrac hcoef
    dsimp [densityMeshPoint]
    calc
      b + ((1 / 2 : ℝ) - κ - b) * (((i + 1 : ℕ) : ℝ) / (N : ℝ)) ≤
          b + ((1 / 2 : ℝ) - κ - b) := by nlinarith
      _ = (1 / 2 : ℝ) - κ := by ring
      _ ≤ 1 := by linarith
  exact primeExponentBin_mem_of_bounds hx hγ'le hp hprimeLower hprimeUpper

def siftedContribution (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b : ℝ) (u : ℕ) : ℝ :=
  if ∀ p ∈ (primesUpTo (x ^ b)).erase 2, ¬ p ∣ 2 * u + 1 then
    C.weighted x jstar u else 0

def primeContribution (C : CandidateData) (x : ℝ) (jstar u : ℕ) : ℝ :=
  if Nat.Prime (2 * u + 1) then C.weighted x jstar u else 0

def balancedContribution (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (κ : ℝ) (u : ℕ) : ℝ :=
  if ¬ Nat.Prime (2 * u + 1) ∧
      x ^ ((1 / 2 : ℝ) - κ) < (Nat.minFac (2 * u + 1) : ℝ) then
    C.weighted x jstar u else 0

lemma meshPointWeight_nonneg (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N : ℕ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u)
    (z : Σ i : ℕ, ℕ × ℕ) : 0 ≤ meshPointWeight C x jstar b κ N z := by
  unfold meshPointWeight
  apply mul_nonneg (hweight z.2.1)
  by_cases hrough : Analytic.rough
      (x ^ densityMeshPoint b κ N z.1) ((2 * z.2.1 + 1) / z.2.2)
  · simp [test, hrough]
  · simp [test, hrough]

lemma meshContribution_nonneg (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N u : ℕ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u) :
    0 ≤ meshContribution C x jstar b κ N u := by
  unfold meshContribution
  apply Finset.sum_nonneg
  intro z hz
  split_ifs
  · exact meshPointWeight_nonneg C x jstar b κ N hweight z
  · norm_num

lemma primeContribution_nonneg (C : CandidateData) (x : ℝ) (jstar u : ℕ)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u) :
    0 ≤ primeContribution C x jstar u := by
  unfold primeContribution
  split_ifs
  · exact hweight u
  · norm_num

lemma balancedContribution_nonneg (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (κ : ℝ) (u : ℕ) (hweight : ∀ u, 0 ≤ C.weighted x jstar u) :
    0 ≤ balancedContribution C x jstar κ u := by
  unfold balancedContribution
  split_ifs
  · exact hweight u
  · norm_num

lemma sum_primeContribution_eq (C : CandidateData) (x : ℝ) (jstar : ℕ) :
    (∑ u ∈ candidateRange x, primeContribution C x jstar u) =
      C.primeMass x jstar := by
  simp [primeContribution, CandidateData.primeMass, candidateRange,
    Finset.sum_filter]

lemma sum_balancedContribution_eq (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (κ : ℝ) :
    (∑ u ∈ candidateRange x, balancedContribution C x jstar κ u) =
      balancedCompositeMass C x jstar κ := by
  simp [balancedContribution, balancedCompositeMass, candidateRange,
    Finset.sum_filter]

lemma primeExponentBin_power_bounds {x γ γ' : ℝ} {p : ℕ}
    (hx : 3 ≤ x) (hp : p ∈ primeExponentBin γ γ' x) :
    x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' := by
  simp [primeExponentBin, hx] at hp
  exact hp.2.2

lemma siftedContribution_le (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N : ℕ) (u : ℕ)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 50) (hbκ : b < κ)
    (hN : 0 < N) (hx : 3 ≤ x) (hu : u ∈ candidateRange x)
    (hweight : ∀ u, 0 ≤ C.weighted x jstar u) :
    siftedContribution C x jstar b u ≤
      primeContribution C x jstar u + meshContribution C x jstar b κ N u +
        balancedContribution C x jstar κ u := by
  have hmeshNonneg := meshContribution_nonneg C x jstar b κ N u hweight
  have hprimeNonneg := primeContribution_nonneg C x jstar u hweight
  have hbalancedNonneg := balancedContribution_nonneg C x jstar κ u hweight
  by_cases hsurv : ∀ p ∈ (primesUpTo (x ^ b)).erase 2, ¬ p ∣ 2 * u + 1
  · by_cases hprime : Nat.Prime (2 * u + 1)
    · have hsift : siftedContribution C x jstar b u = C.weighted x jstar u := by
        unfold siftedContribution
        rw [if_pos hsurv]
      have hprimeEq : primeContribution C x jstar u = C.weighted x jstar u := by
        simp [primeContribution, hprime]
      rw [hsift, hprimeEq]
      linarith
    · let p : ℕ := Nat.minFac (2 * u + 1)
      have huIcc : u ∈ Finset.Icc 1 ⌊2 * x⌋₊ := by
        simpa [candidateRange] using hu
      have huLower : 1 ≤ u := (Finset.mem_Icc.mp huIcc).1
      have hNtwo : 2 ≤ 2 * u + 1 := by omega
      have hp : Nat.Prime p := by
        dsimp [p]
        exact Nat.minFac_prime (by omega)
      have hpdiv : p ∣ 2 * u + 1 := by
        dsimp [p]
        exact Nat.minFac_dvd _
      have hY : 1 ≤ x ^ b := by
        have hY' : 1 < x ^ b := Real.one_lt_rpow (by linarith) hb
        linarith
      have hpLower : x ^ b < (p : ℝ) := by
        exact survivor_prime_factor_gt (x ^ b) u p hY hp hpdiv hsurv
      have hprimeEq : primeContribution C x jstar u = 0 := by
        unfold primeContribution
        rw [if_neg hprime]
      have hsift : siftedContribution C x jstar b u = C.weighted x jstar u := by
        unfold siftedContribution
        rw [if_pos hsurv]
      by_cases hlow : (Nat.minFac (2 * u + 1) : ℝ) ≤
          x ^ ((1 / 2 : ℝ) - κ)
      · obtain ⟨i, hi, hbin⟩ := exists_densityMeshBin hx hb hκ hκsmall hbκ hN hp
          hpLower (by simpa [p] using hlow)
        have hbinPower := primeExponentBin_power_bounds hx hbin
        have hrough : Analytic.rough
            (x ^ densityMeshPoint b κ N i) ((2 * u + 1) / p) := by
          have hrough' := minFac_cofactor_rough
            (N := 2 * u + 1) hNtwo (by simpa [p] using hbinPower.1)
          simpa [p] using hrough'
        have htest : test (.rough (densityMeshPoint b κ N i)) x
            ((2 * u + 1) / p) = 1 := by
          simp [test, hrough]
        have hpair : (u, p) ∈ meshSlice x b κ N i := by
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_product.mpr ⟨hu, hbin⟩
          · exact hpdiv
        have hq : (⟨i, (u, p)⟩ : Σ i : ℕ, ℕ × ℕ) ∈ meshIndexSet x b κ N :=
          Finset.mem_sigma.mpr ⟨hi, hpair⟩
        have hqU : (⟨i, (u, p)⟩ : Σ i : ℕ, ℕ × ℕ).2.1 = u := rfl
        have hqWeight : meshPointWeight C x jstar b κ N
            (⟨i, (u, p)⟩ : Σ i : ℕ, ℕ × ℕ) = C.weighted x jstar u := by
          simp [meshPointWeight, htest]
        have htermsNonneg : ∀ z ∈ meshIndexSet x b κ N,
            0 ≤ if z.2.1 = u then meshPointWeight C x jstar b κ N z else 0 := by
          intro z hz
          split_ifs
          · exact meshPointWeight_nonneg C x jstar b κ N hweight z
          · norm_num
        have hsingle := Finset.single_le_sum htermsNonneg hq
        have hmeshCover : C.weighted x jstar u ≤
            meshContribution C x jstar b κ N u := by
          simpa [meshContribution, hqU, hqWeight] using hsingle
        have hbalEq : balancedContribution C x jstar κ u = 0 := by
          have hfalse : ¬ (¬ Nat.Prime (2 * u + 1) ∧
              x ^ ((1 / 2 : ℝ) - κ) <
                (Nat.minFac (2 * u + 1) : ℝ)) := by
            intro hh
            exact (not_lt_of_ge hlow) hh.2
          unfold balancedContribution
          rw [if_neg hfalse]
        rw [hsift, hprimeEq, hbalEq]
        linarith [hmeshCover]
      · have hlow' : x ^ ((1 / 2 : ℝ) - κ) <
          (Nat.minFac (2 * u + 1) : ℝ) := lt_of_not_ge hlow
        have hbalEq : balancedContribution C x jstar κ u = C.weighted x jstar u := by
          unfold balancedContribution
          rw [if_pos ⟨hprime, hlow'⟩]
        rw [hsift, hprimeEq, hbalEq]
        linarith
  · have hsift : siftedContribution C x jstar b u = 0 := by
      unfold siftedContribution
      rw [if_neg hsurv]
    rw [hsift]
    linarith

lemma sum_siftedContribution_le (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N : ℕ) (hb : 0 < b) (hκ : 0 < κ)
    (hκsmall : κ < 1 / 50) (hbκ : b < κ) (hN : 0 < N)
    (hx : 3 ≤ x) (hweight : ∀ u, 0 ≤ C.weighted x jstar u) :
    candidateSiftedMass C x jstar (x ^ b) ≤
      C.primeMass x jstar + unbalancedMeshMass C x jstar b κ N +
        balancedCompositeMass C x jstar κ := by
  have hsum := Finset.sum_le_sum (s := candidateRange x)
    (fun u hu => siftedContribution_le C x jstar b κ N u hb hκ hκsmall
      hbκ hN hx hu hweight)
  change (∑ u ∈ candidateRange x, siftedContribution C x jstar b u) ≤ _ at hsum
  calc
    candidateSiftedMass C x jstar (x ^ b) =
        ∑ u ∈ candidateRange x, siftedContribution C x jstar b u := by
          simp [candidateSiftedMass, candidateRange, siftedContribution]
    _ ≤ ∑ u ∈ candidateRange x,
        (primeContribution C x jstar u + meshContribution C x jstar b κ N u +
          balancedContribution C x jstar κ u) := hsum
    _ = C.primeMass x jstar + unbalancedMeshMass C x jstar b κ N +
        balancedCompositeMass C x jstar κ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            sum_primeContribution_eq, sum_meshContribution_eq,
            sum_balancedContribution_eq]

 theorem CompositeCoverageTask_proof :
    CompositeCoverageTask := by
  intro δ C hBounds b κ hb hbκ hκ hκsmall N hN jstar hj
  rcases hBounds with ⟨K, CA, cmin, cmax, hK, hcmin, hcmax, hmass⟩
  filter_upwards [hmass jstar hj, Filter.eventually_ge_atTop (3 : ℝ)]
    with x hmassx hx
  rcases hmassx with ⟨_, _, _, hweight, _, _⟩
  exact sum_siftedContribution_le C x jstar b κ N hb hκ hκsmall hbκ hN hx hweight


end Erdos821.S10Cover
