import Erdos821.P6Sq.EndpointSquareTask
import Erdos821.P6Off.ShiftEndpoints
import Erdos821.P6Off.Rough
import Erdos821.P6Off.Discrepancy

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Sq
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- Verbatim local copy of the absolute Fourier-error mass from `TailTask`. -/
def absoluteDeterminantDyad (P : Geometry) (G : PrimeGroups) (x U Z lo hi rho sigma : ℝ)
    (N : ℕ) (k : ℤ) (psi : ℝ → ℝ) (c alpha : ℕ → ℂ) : ℝ :=
  ∑ z ∈ Finset.Icc 1 N, ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
    if 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat then
      ‖(psi (z / Z) : ℂ) *
        (alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
          star (alpha m' * hCoefficient P G x lo hi rho sigma c (((z : ℤ) + k).toNat / m))‖
    else 0

/-- Local copy of the §5 absolute dyad task. -/
def AbsoluteDeterminantDyadTask : Prop :=
  ClassicalInputs → EndpointSquareTask → ∀ (P : Geometry) (C : ℝ), 0 < C →
    ∃ C' K : ℝ, 0 < C' ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (U Z lo hi rho sigma : ℝ)
        (N : ℕ) (k : ℤ) (psi : ℝ → ℝ) (c alpha : ℕ → ℂ),
        Admissible P x G → 0 < U → 1 ≤ Z → 3 * Z ≤ x ^ (2 : ℕ) →
        |(k : ℝ)| ≤ Z →
        Function.support psi ⊆ Set.Icc (1 / 2) 2 → (∀ t, |psi t| ≤ 1) →
        (∀ n, ‖alpha n‖ ≤ L x ^ C ∧ ‖c n‖ ≤ L x ^ C) →
        (∀ n, alpha n ≠ 0 → rough (W x) n) →
        absoluteDeterminantDyad P G x U Z lo hi rho sigma N k psi c alpha ≤
          K * Z * L x ^ C'

private def normSeq (a : ℕ → ℂ) : ℕ → ℂ := fun n => (‖a n‖ : ℂ)

private def absCoreReal (x lo hi : ℝ) (c : ℕ → ℂ) (t : ℕ) : ℝ :=
  ∑ pr ∈ t.divisorsAntidiagonal,
    if lo ≤ (pr.1 : ℝ) ∧ (pr.1 : ℝ) ≤ hi ∧ rough (W x) pr.1 then ‖c pr.2‖ else 0

private def absHReal (P : Geometry) (G : PrimeGroups) (x lo hi : ℝ)
    (c : ℕ → ℂ) (n : ℕ) : ℝ :=
  markWeight G P.q (fun _ => P.ell) n * absCoreReal x lo hi c (groupFreePart G n)

private def absFactor (U : ℝ) (c alpha : ℕ → ℂ) (P : Geometry) (G : PrimeGroups)
    (x lo hi : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ dyad U, if m ∣ n then ‖alpha m‖ * absHReal P G x lo hi c (n / m) else 0

private theorem absCoreReal_nonneg (x lo hi : ℝ) (c : ℕ → ℂ) (t : ℕ) :
    0 ≤ absCoreReal x lo hi c t := by
  unfold absCoreReal
  apply Finset.sum_nonneg
  intro pr hpr
  split_ifs <;> positivity

private theorem absHReal_nonneg (P : Geometry) (G : PrimeGroups) (x lo hi : ℝ)
    (hG : Admissible P x G) (c : ℕ → ℂ) (n : ℕ) :
    0 ≤ absHReal P G x lo hi c n := by
  unfold absHReal
  exact mul_nonneg (Erdos821.P6Sq.markWeight_nonneg P G x hG n)
    (absCoreReal_nonneg x lo hi c _)

private theorem hCoefficient_norm_le_absHReal (P : Geometry) (G : PrimeGroups)
    (x lo hi rho sigma : ℝ) (hG : Admissible P x G) (c : ℕ → ℂ) (n : ℕ) :
    ‖hCoefficient P G x lo hi rho sigma c n‖ ≤ absHReal P G x lo hi c n := by
  have hw := Erdos821.P6Sq.markWeight_nonneg P G x hG n
  have hcore :
      ‖roughCore x lo hi sigma c (groupFreePart G n)‖ ≤
        absCoreReal x lo hi c (groupFreePart G n) := by
    unfold roughCore absCoreReal
    calc
      _ ≤ ∑ pr ∈ (groupFreePart G n).divisorsAntidiagonal,
          ‖if lo ≤ (pr.1 : ℝ) ∧ (pr.1 : ℝ) ≤ hi ∧ rough (W x) pr.1 then
              mellin pr.1 sigma * c pr.2 else 0‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro pr hpr
        split_ifs <;> simp [norm_mul, Erdos821.P5Core.norm_mellin]
  unfold hCoefficient absHReal
  rw [norm_mul, norm_mul]
  have hw' : ‖(markWeight G P.q (fun _ => P.ell) n : ℂ)‖ =
      markWeight G P.q (fun _ => P.ell) n := by
    simp [Complex.norm_real, abs_of_nonneg hw]
  rw [Erdos821.P5Core.norm_mellin, hw', one_mul]
  exact mul_le_mul_of_nonneg_left hcore hw

private theorem hCoefficient_normSeq_eq_absHReal (P : Geometry) (G : PrimeGroups)
    (x lo hi : ℝ) (hG : Admissible P x G) (c : ℕ → ℂ) (n : ℕ) :
    hCoefficient P G x lo hi 0 0 (normSeq c) n = (absHReal P G x lo hi c n : ℂ) := by
  have hcore : roughCore x lo hi 0 (normSeq c) (groupFreePart G n) =
      (absCoreReal x lo hi c (groupFreePart G n) : ℂ) := by
    unfold roughCore absCoreReal
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro pr hpr
    split_ifs <;> simp [normSeq, Erdos821.Blueprint.Analytic.mellin]
  unfold hCoefficient absHReal
  rw [show Erdos821.Blueprint.Analytic.mellin n 0 = 1 by
    simp [Erdos821.Blueprint.Analytic.mellin], hcore]
  simp only [Complex.ofReal_mul, one_mul]

private theorem absFactor_nonneg (U : ℝ) (c alpha : ℕ → ℂ) (P : Geometry)
    (G : PrimeGroups) (x lo hi : ℝ) (hG : Admissible P x G) (n : ℕ) :
    0 ≤ absFactor U c alpha P G x lo hi n := by
  unfold absFactor
  apply Finset.sum_nonneg
  intro m hm
  split_ifs with hdiv
  · exact mul_nonneg (norm_nonneg _) (absHReal_nonneg P G x lo hi hG c (n / m))
  · exact le_rfl

private theorem absFactor_endpoint_eq (P : Geometry) (G : PrimeGroups)
    (x U lo hi : ℝ) (hU : 0 < U) (hG : Admissible P x G)
    (hxL : 1 ≤ L x) (c alpha : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hfree : ∀ m, normSeq alpha m ≠ 0 → GroupFree G m) :
    (absFactor U c alpha P G x lo hi n : ℂ) =
      endpoint G x
        (Erdos821.P6Off.shiftEndpoint U lo hi 0 0 0 (normSeq c) (normSeq alpha)
          1 (by norm_num) 1) n * (markWeight G P.q (fun _ => P.ell) n : ℂ) := by
  let F := Erdos821.P6Off.shiftEndpoint U lo hi 0 0 0 (normSeq c) (normSeq alpha)
    1 (by norm_num) 1
  have hid := Erdos821.P6Off.shiftEndpoint_identity P G x U lo hi 0 0 0
    (normSeq c) (normSeq alpha) 1 (by norm_num) 1 n hn hfree
  have htrivial : ∀ m : ℕ, (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 := by
    intro m
    have hm1 : (m : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hm1]
    exact map_one _
  have hanti :
      endpoint G x F n * (markWeight G P.q (fun _ => P.ell) n : ℂ) =
        ∑ m ∈ n.divisors,
          Erdos821.Blueprint.restricted U (normSeq alpha) m *
            hCoefficient P G x lo hi 0 0 (normSeq c) (n / m) := by
    rw [Nat.sum_divisorsAntidiagonal
      (fun m h => (Erdos821.Blueprint.restricted U (normSeq alpha) m *
        (1 : DirichletCharacter ℂ 1) (m : ZMod 1) * mellin m 0) *
          star (hCoefficient P G x lo hi 0 0 (normSeq c) h))] at hid
    simpa [F, Erdos821.P6Off.shiftEndpoint, Erdos821.Blueprint.Analytic.mellin,
      htrivial, hCoefficient_normSeq_eq_absHReal P G x lo hi hG c] using hid
  have hfactor :
      (absFactor U c alpha P G x lo hi n : ℂ) =
        ∑ m ∈ n.divisors,
          Erdos821.Blueprint.restricted U (normSeq alpha) m *
            hCoefficient P G x lo hi 0 0 (normSeq c) (n / m) := by
    unfold absFactor
    rw [← Finset.sum_filter]
    let s₁ := (dyad U).filter (fun m => m ∣ n)
    let s₂ := n.divisors.filter (fun m => m ∈ dyad U)
    have hs : s₁ = s₂ := by
      ext m
      simp only [s₁, s₂, Finset.mem_filter]
      change (m ∈ dyad U ∧ m ∣ n) ↔ (m ∈ n.divisors ∧ m ∈ dyad U)
      constructor
      · rintro ⟨hm, hmn⟩
        exact ⟨Nat.mem_divisors.mpr ⟨hmn, hn⟩, hm⟩
      · rintro ⟨hmdiv, hm⟩
        exact ⟨hm, (Nat.mem_divisors.mp hmdiv).1⟩
    change (((∑ m ∈ s₁, ‖alpha m‖ * absHReal P G x lo hi c (n / m) : ℝ) : ℂ)) = _
    rw [Complex.ofReal_sum, hs]
    have hlocal :
        (∑ m ∈ s₂,
          Erdos821.Blueprint.restricted U (normSeq alpha) m *
            hCoefficient P G x lo hi 0 0 (normSeq c) (n / m)) =
          ∑ m ∈ s₂, ((‖alpha m‖ * absHReal P G x lo hi c (n / m) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmD : m ∈ dyad U := (Finset.mem_filter.mp hm).2
      have hmres : Erdos821.Blueprint.restricted U (normSeq alpha) m = normSeq alpha m := by
        exact if_pos ((Erdos821.P6Off.mem_dyad_iff U m).mp hmD)
      rw [hmres, hCoefficient_normSeq_eq_absHReal P G x lo hi hG c]
      simp [normSeq, Complex.ofReal_mul]
    calc
      (∑ m ∈ s₂,
        ((‖alpha m‖ * absHReal P G x lo hi c (n / m) : ℝ) : ℂ)) =
          ∑ m ∈ s₂,
            Erdos821.Blueprint.restricted U (normSeq alpha) m *
              hCoefficient P G x lo hi 0 0 (normSeq c) (n / m) := hlocal.symm
      _ = ∑ m ∈ n.divisors,
            Erdos821.Blueprint.restricted U (normSeq alpha) m *
              hCoefficient P G x lo hi 0 0 (normSeq c) (n / m) := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro m hm hmnot
          have hmD : m ∉ dyad U := by
            intro hmD
            exact hmnot (Finset.mem_filter.mpr ⟨hm, hmD⟩)
          have hres : Erdos821.Blueprint.restricted U (normSeq alpha) m = 0 := by
            unfold Erdos821.Blueprint.restricted
            split_ifs with h
            · exact False.elim (hmD ((Erdos821.P6Off.mem_dyad_iff U m).mpr h))
            · rfl
          simp [hres]
  calc
    (absFactor U c alpha P G x lo hi n : ℂ) =
        ∑ m ∈ n.divisors,
          Erdos821.Blueprint.restricted U (normSeq alpha) m *
            hCoefficient P G x lo hi 0 0 (normSeq c) (n / m) := hfactor
    _ = endpoint G x F n * (markWeight G P.q (fun _ => P.ell) n : ℂ) := hanti.symm

private theorem absFactor_eq_endpoint_norm (P : Geometry) (G : PrimeGroups)
    (x U lo hi : ℝ) (hU : 0 < U) (hG : Admissible P x G)
    (hxL : 1 ≤ L x) (c alpha : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hfree : ∀ m, normSeq alpha m ≠ 0 → GroupFree G m) :
    absFactor U c alpha P G x lo hi n =
      ‖endpoint G x
        (Erdos821.P6Off.shiftEndpoint U lo hi 0 0 0 (normSeq c) (normSeq alpha)
          1 (by norm_num) 1) n * (markWeight G P.q (fun _ => P.ell) n : ℂ)‖ := by
  have hEq := absFactor_endpoint_eq P G x U lo hi hU hG hxL c alpha n hn hfree
  have hnonneg := absFactor_nonneg U c alpha P G x lo hi hG n
  calc
    absFactor U c alpha P G x lo hi n = ‖(absFactor U c alpha P G x lo hi n : ℂ)‖ := by
      simp [Complex.norm_real, abs_of_nonneg hnonneg]
    _ = ‖endpoint G x
        (Erdos821.P6Off.shiftEndpoint U lo hi 0 0 0 (normSeq c) (normSeq alpha)
          1 (by norm_num) 1) n * (markWeight G P.q (fun _ => P.ell) n : ℂ)‖ := by
      rw [hEq]

private theorem absCross_pair_le (P : Geometry) (G : PrimeGroups)
    (x U lo hi rho sigma : ℝ) (hG : Admissible P x G) (c alpha : ℕ → ℂ)
    (z : ℕ) (k : ℤ) (hzshift : 0 < (z : ℤ) + k)
    (z' : ℕ) (hz' : z' = ((z : ℤ) + k).toNat) :
    (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
      if 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat then
        ‖(alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
          star (alpha m' * hCoefficient P G x lo hi rho sigma c (z' / m))‖
      else 0) ≤
      absFactor U c alpha P G x lo hi z' * absFactor U c alpha P G x lo hi z := by
  have hterms (m m' : ℕ) :
      (if 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat then
        ‖(alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
          star (alpha m' * hCoefficient P G x lo hi rho sigma c (z' / m))‖
      else 0) ≤
        (if m ∣ z' then ‖alpha m‖ * absHReal P G x lo hi c (z' / m) else 0) *
          (if m' ∣ z then ‖alpha m'‖ * absHReal P G x lo hi c (z / m') else 0) := by
    by_cases hm : m ∣ z'
    · by_cases hm' : m' ∣ z
      · have hnorm :
            ‖(alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
              star (alpha m' * hCoefficient P G x lo hi rho sigma c (z' / m))‖ =
              (‖alpha m‖ * ‖hCoefficient P G x lo hi rho sigma c (z / m')‖) *
                (‖alpha m'‖ * ‖hCoefficient P G x lo hi rho sigma c (z' / m)‖) := by
          simp only [norm_mul, norm_star]
        have hleft := hCoefficient_norm_le_absHReal P G x lo hi rho sigma hG c (z / m')
        have hright := hCoefficient_norm_le_absHReal P G x lo hi rho sigma hG c (z' / m)
        have hleft' := mul_le_mul_of_nonneg_left hleft (norm_nonneg (alpha m))
        have hright' := mul_le_mul_of_nonneg_left hright (norm_nonneg (alpha m'))
        have hB : 0 ≤ ‖alpha m'‖ * ‖hCoefficient P G x lo hi rho sigma c (z' / m)‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have hA' : 0 ≤ ‖alpha m‖ * absHReal P G x lo hi c (z / m') :=
          mul_nonneg (norm_nonneg _) (absHReal_nonneg P G x lo hi hG c _)
        rw [if_pos ⟨hzshift, hm', by simpa [hz'] using hm⟩,
          if_pos hm, if_pos hm']
        calc
          _ = (‖alpha m‖ * ‖hCoefficient P G x lo hi rho sigma c (z / m')‖) *
                (‖alpha m'‖ * ‖hCoefficient P G x lo hi rho sigma c (z' / m)‖) := hnorm
          _ ≤ (‖alpha m‖ * absHReal P G x lo hi c (z / m')) *
                (‖alpha m'‖ * absHReal P G x lo hi c (z' / m)) :=
            mul_le_mul hleft' hright' hB hA'
          _ = (‖alpha m‖ * absHReal P G x lo hi c (z' / m)) *
                (‖alpha m'‖ * absHReal P G x lo hi c (z / m')) := by ring
      · simp [hzshift, hm, hm', hz']
    · have hmNat : ¬ m ∣ ((z : ℤ) + k).toNat := by
        rw [← hz']
        exact hm
      simp [hzshift, hm, hmNat]
  calc
    _ ≤ ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        (if m ∣ z' then ‖alpha m‖ * absHReal P G x lo hi c (z' / m) else 0) *
          (if m' ∣ z then ‖alpha m'‖ * absHReal P G x lo hi c (z / m') else 0) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro m' hm'
      exact hterms m m'
    _ = absFactor U c alpha P G x lo hi z' * absFactor U c alpha P G x lo hi z := by
      rw [← Finset.sum_mul_sum]
      rfl

theorem absoluteDeterminantDyadTask_proof : AbsoluteDeterminantDyadTask := by
  intro inputs hEndpointSquare P C hC
  obtain ⟨C', K, hC', hK, hEndpointSquare⟩ := hEndpointSquare inputs P C hC
  let Kfinal := 3 * K
  refine ⟨C', Kfinal, hC', ?_, ?_⟩
  · dsimp [Kfinal]
    positivity
  filter_upwards [hEndpointSquare,
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hxSquare hxL
  intro G U Z lo hi rho sigma N k psi c alpha hG hU hZ h3Z hk hsupport hpsi hcoeff hrough
  let M : ℕ := ⌊3 * Z⌋₊
  let F := Erdos821.P6Off.shiftEndpoint U lo hi 0 0 0 (normSeq c) (normSeq alpha)
    1 (by norm_num) 1
  let q (z : ℕ) : ℕ := ((z : ℤ) + k).toNat
  let g (n : ℕ) : ℝ :=
    ‖endpoint G x F n * (markWeight G P.q (fun _ => P.ell) n : ℂ)‖
  let S : Finset ℕ := (Finset.Icc 1 N).filter (fun z =>
    psi ((z : ℝ) / Z) ≠ 0 ∧ 0 < (z : ℤ) + k)
  let T (z : ℕ) : ℝ :=
    ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
      if 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat then
        ‖((psi ((z : ℝ) / Z) : ℂ) *
          (alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
            star (alpha m' * hCoefficient P G x lo hi rho sigma c (q z / m)) )‖
      else 0
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hxL
  have hPowpos : 0 < L x ^ C := Real.rpow_pos_of_pos hLpos C
  have hPownonneg : 0 ≤ L x ^ C := hPowpos.le
  have hMcast : (M : ℝ) ≤ 3 * Z := by
    dsimp [M]
    exact Nat.floor_le (by positivity)
  have hMle : (M : ℝ) ≤ x ^ (2 : ℕ) := hMcast.trans h3Z
  have hAlphaNorm : ∀ n, ‖normSeq alpha n‖ ≤ L x ^ C := by
    intro n
    simpa [normSeq] using (hcoeff n).1
  have hCNorm : ∀ n, ‖normSeq c n‖ ≤ L x ^ C := by
    intro n
    simpa [normSeq] using (hcoeff n).2
  have hRestricted := Erdos821.P6Off.restricted_bound U (L x ^ C) (normSeq alpha)
    hPownonneg hAlphaNorm
  have hFcoeff : ∀ n, ‖F.alpha n‖ ≤ L x ^ C ∧ ‖F.residual n‖ ≤ L x ^ C := by
    intro n
    constructor
    · change ‖Erdos821.Blueprint.restricted U (normSeq alpha) n‖ ≤ L x ^ C
      exact hRestricted n
    · change ‖star (normSeq c n)‖ ≤ L x ^ C
      simpa using hCNorm n
  have hAlphaRough : ∀ n, normSeq alpha n ≠ 0 → rough (W x) n := by
    intro n hn
    apply hrough n
    intro hzero
    apply hn
    simp [normSeq, hzero]
  have hfree : ∀ m, normSeq alpha m ≠ 0 → GroupFree G m := by
    intro m hm
    exact Erdos821.P6Off.rough_groupFree P x G hxL hG m (hAlphaRough m hm)
  have hSquare := hxSquare G F M hG hMle hFcoeff
  have hSsub : S ⊆ Finset.Icc 1 M := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzN, hpsiNZ, hzshift⟩
    have hrange := hsupport hpsiNZ
    have hzupper : (z : ℝ) ≤ 2 * Z := by
      apply (div_le_iff₀ (by linarith : 0 < Z)).mp
      exact hrange.2
    have hzfloor : z ≤ M := by
      change z ≤ ⌊3 * Z⌋₊
      apply Nat.le_floor
      linarith
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hzN).1, hzfloor⟩
  have hqcastInt (z : ℕ) (hzshift : 0 < (z : ℤ) + k) :
      ((q z : ℕ) : ℤ) = (z : ℤ) + k := by
    dsimp [q]
    exact Int.toNat_of_nonneg hzshift.le
  have hShiftInjective : ∀ a ∈ S, ∀ b ∈ S, q a = q b → a = b := by
    intro a ha b hb hab
    have haShift := (Finset.mem_filter.mp ha).2.2
    have hbShift := (Finset.mem_filter.mp hb).2.2
    have haCast := hqcastInt a haShift
    have hbCast := hqcastInt b hbShift
    have habInt : (q a : ℤ) = (q b : ℤ) := congrArg Int.ofNat hab
    rw [haCast, hbCast] at habInt
    omega
  have hSimageSub : S.image q ⊆ Finset.Icc 1 M := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    rcases Finset.mem_filter.mp hz with ⟨hzN, hpsiNZ, hzshift⟩
    have hrange := hsupport hpsiNZ
    have hzupper : (z : ℝ) ≤ 2 * Z := by
      apply (div_le_iff₀ (by linarith : 0 < Z)).mp
      exact hrange.2
    have hqR : (q z : ℝ) = (z : ℝ) + (k : ℝ) := by
      exact_mod_cast hqcastInt z hzshift
    have hqUpper : (q z : ℝ) ≤ 3 * Z := by
      rw [hqR]
      calc
        (z : ℝ) + (k : ℝ) ≤ (z : ℝ) + |(k : ℝ)| := by linarith [le_abs_self (k : ℝ)]
        _ ≤ 2 * Z + Z := by nlinarith [hzupper, hk]
        _ = 3 * Z := by ring
    have hqFloor : q z ≤ M := by
      change q z ≤ ⌊3 * Z⌋₊
      exact Nat.le_floor hqUpper
    have hqpos : 1 ≤ q z := by
      have hqInt : (0 : ℤ) < (q z : ℤ) := by
        rw [hqcastInt z hzshift]
        exact hzshift
      exact_mod_cast hqInt
    exact Finset.mem_Icc.mpr ⟨hqpos, hqFloor⟩
  have hSsum : (∑ z ∈ Finset.Icc 1 N, T z) ≤ ∑ z ∈ S, g z * g (q z) := by
    have hpoint (z : ℕ) (hz : z ∈ Finset.Icc 1 N) :
        T z ≤ if z ∈ S then g z * g (q z) else 0 := by
      by_cases hpsiNZ : psi ((z : ℝ) / Z) = 0
      · simp [T, S, hpsiNZ]
      by_cases hzshift : 0 < (z : ℤ) + k
      · have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hz, hpsiNZ, hzshift⟩
        have hpair := absCross_pair_le P G x U lo hi rho sigma hG c alpha z k hzshift
          (q z) rfl
        have hinner :
            T z ≤
              (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
                if 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat then
                  ‖(alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
                    star (alpha m' * hCoefficient P G x lo hi rho sigma c (q z / m))‖
                else 0) := by
          unfold T
          apply Finset.sum_le_sum
          intro m hm
          apply Finset.sum_le_sum
          intro m' hm'
          by_cases hcond : 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat
          · rw [if_pos hcond, if_pos hcond]
            have hpsiBound := hpsi ((z : ℝ) / Z)
            let A := alpha m * hCoefficient P G x lo hi rho sigma c (z / m')
            let B := star (alpha m' * hCoefficient P G x lo hi rho sigma c (q z / m))
            have hterm : ‖((psi ((z : ℝ) / Z) : ℂ) * A) * B‖ ≤ ‖A * B‖ := by
              calc
                _ = |psi ((z : ℝ) / Z)| * ‖A‖ * ‖B‖ := by
                  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                _ ≤ 1 * ‖A‖ * ‖B‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hpsiBound (norm_nonneg A))
                    (norm_nonneg B)
                _ = ‖A * B‖ := by simp [norm_mul]
            simpa [A, B] using hterm
          · simp [hcond]
        have hzposNat : 0 < z := by
          exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hz).1
        have hfactorZ := absFactor_eq_endpoint_norm P G x U lo hi hU hG hxL c alpha z
          hzposNat.ne' hfree
        have hqpos : 0 < q z := by
          have hqInt : (0 : ℤ) < (q z : ℤ) := by
            rw [hqcastInt z hzshift]
            exact hzshift
          exact_mod_cast hqInt
        have hfactorShift := absFactor_eq_endpoint_norm P G x U lo hi hU hG hxL c alpha
          (q z) hqpos.ne' hfree
        have hgZ : absFactor U c alpha P G x lo hi z = g z := by
          change absFactor U c alpha P G x lo hi z =
            ‖endpoint G x F z * (markWeight G P.q (fun _ => P.ell) z : ℂ)‖
          exact hfactorZ
        have hgShift : absFactor U c alpha P G x lo hi (q z) = g (q z) := by
          change absFactor U c alpha P G x lo hi (q z) =
            ‖endpoint G x F (q z) * (markWeight G P.q (fun _ => P.ell) (q z) : ℂ)‖
          exact hfactorShift
        have hbound : T z ≤ g z * g (q z) := by
          calc
            T z ≤ absFactor U c alpha P G x lo hi (q z) *
                absFactor U c alpha P G x lo hi z := hinner.trans hpair
            _ = g (q z) * g z := by rw [hgShift, hgZ]
            _ = g z * g (q z) := by ring
        simpa [hzS] using hbound
      · have hzNotS : z ∉ S := by
          intro hzS
          exact hzshift (Finset.mem_filter.mp hzS).2.2
        simp [T, hzNotS, hzshift]
    calc
      _ ≤ ∑ z ∈ Finset.Icc 1 N, if z ∈ S then g z * g (q z) else 0 := by
        apply Finset.sum_le_sum
        intro z hz
        exact hpoint z hz
      _ = ∑ z ∈ S, g z * g (q z) := by
        calc
          _ = ∑ z ∈ Finset.Icc 1 N,
              if psi ((z : ℝ) / Z) ≠ 0 ∧ 0 < (z : ℤ) + k then
                g z * g (q z) else 0 := by
                apply Finset.sum_congr rfl
                intro z hz
                simp [S, hz]
          _ = ∑ z ∈ S, g z * g (q z) := by
                rw [← Finset.sum_filter]
  have hFirstSq :
      (∑ z ∈ S, g z ^ (2 : ℕ)) ≤
        ∑ n ∈ Finset.Icc 1 M, g n ^ (2 : ℕ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
    intro n hn hnot
    positivity
  have hShiftedSq :
      (∑ z ∈ S, g (q z) ^ (2 : ℕ)) ≤
        ∑ n ∈ Finset.Icc 1 M, g n ^ (2 : ℕ) := by
    calc
      _ = ∑ n ∈ S.image q, g n ^ (2 : ℕ) := by
        rw [Finset.sum_image hShiftInjective]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hSimageSub
        intro n hn hnot
        positivity
  have hCS :
      (∑ z ∈ S, g z * g (q z)) ^ (2 : ℕ) ≤
        (∑ z ∈ S, g z ^ (2 : ℕ)) * (∑ z ∈ S, g (q z) ^ (2 : ℕ)) :=
    Finset.sum_mul_sq_le_sq_mul_sq S g (fun z => g (q z))
  have hProdNonneg : 0 ≤ ∑ z ∈ S, g z * g (q z) := by
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hRootCS :
      (∑ z ∈ S, g z * g (q z)) ≤
        Real.sqrt (∑ z ∈ S, g z ^ (2 : ℕ)) *
          Real.sqrt (∑ z ∈ S, g (q z) ^ (2 : ℕ)) := by
    have hrootSq := Real.sqrt_sq_eq_abs (∑ z ∈ S, g z * g (q z))
    have hA0 : 0 ≤ ∑ z ∈ S, g z ^ (2 : ℕ) := by
      apply Finset.sum_nonneg
      intro z hz
      positivity
    have hrootMul :
        Real.sqrt ((∑ z ∈ S, g z ^ (2 : ℕ)) *
          (∑ z ∈ S, g (q z) ^ (2 : ℕ))) =
        Real.sqrt (∑ z ∈ S, g z ^ (2 : ℕ)) *
          Real.sqrt (∑ z ∈ S, g (q z) ^ (2 : ℕ)) := by
      exact Real.sqrt_mul hA0 _
    calc
      _ = Real.sqrt ((∑ z ∈ S, g z * g (q z)) ^ (2 : ℕ)) := by
        rw [hrootSq, abs_of_nonneg hProdNonneg]
      _ ≤ Real.sqrt ((∑ z ∈ S, g z ^ (2 : ℕ)) *
          (∑ z ∈ S, g (q z) ^ (2 : ℕ))) := Real.sqrt_le_sqrt hCS
      _ = _ := hrootMul
  have hSquareBound :
      (∑ n ∈ Finset.Icc 1 M, g n ^ (2 : ℕ)) ≤ K * (M : ℝ) * L x ^ C' := by
    simpa [g] using hSquare
  have hBoundNonneg : 0 ≤ K * (M : ℝ) * L x ^ C' := by positivity
  have hRootsBound :
      Real.sqrt (∑ z ∈ S, g z ^ (2 : ℕ)) *
        Real.sqrt (∑ z ∈ S, g (q z) ^ (2 : ℕ)) ≤ K * (M : ℝ) * L x ^ C' := by
    have hA := Real.sqrt_le_sqrt (hFirstSq.trans hSquareBound)
    have hB := Real.sqrt_le_sqrt (hShiftedSq.trans hSquareBound)
    calc
      _ ≤ Real.sqrt (K * (M : ℝ) * L x ^ C') *
          Real.sqrt (K * (M : ℝ) * L x ^ C') :=
        mul_le_mul hA hB (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = K * (M : ℝ) * L x ^ C' := by
        rw [← pow_two, Real.sq_sqrt hBoundNonneg]
  have hAbsolute := hSsum.trans (hRootCS.trans hRootsBound)
  have hMbound : K * (M : ℝ) ≤ (3 * K) * Z := by
    calc
      K * (M : ℝ) ≤ K * (3 * Z) := mul_le_mul_of_nonneg_left hMcast (le_of_lt hK)
      _ = (3 * K) * Z := by ring
  have hFinal : K * (M : ℝ) * L x ^ C' ≤ Kfinal * Z * L x ^ C' := by
    dsimp [Kfinal]
    exact mul_le_mul_of_nonneg_right hMbound (Real.rpow_nonneg (le_of_lt hLpos) C')
  calc
    absoluteDeterminantDyad P G x U Z lo hi rho sigma N k psi c alpha =
        ∑ z ∈ Finset.Icc 1 N, T z := by rfl
    _ ≤ K * (M : ℝ) * L x ^ C' := hAbsolute
    _ ≤ Kfinal * Z * L x ^ C' := hFinal


end Erdos821.P6Sq
