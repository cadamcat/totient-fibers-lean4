import Erdos821.Blueprint.Analytic
import Erdos821.Classical.DivisorMoments
import Erdos821.P5.Basic
import Erdos821.Leaves.MarkSup

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P6Sq
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.Classical
attribute [local instance] Classical.propDecidable

/-- Verbatim local copy of the §5 absolute endpoint task. -/
def EndpointSquareTask : Prop :=
  ClassicalInputs → ∀ (P : Geometry) (C : ℝ), 0 < C →
    ∃ C' K : ℝ, 0 < C' ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (F : Endpoint) (N : ℕ),
        Admissible P x G → (N : ℝ) ≤ x ^ (2 : ℕ) →
        (∀ n, ‖F.alpha n‖ ≤ L x ^ C ∧ ‖F.residual n‖ ≤ L x ^ C) →
        (∑ n ∈ Finset.Icc 1 N,
          ‖endpoint G x F n * (markWeight G P.q (fun _ => P.ell) n : ℂ)‖ ^ 2) ≤
            K * N * L x ^ C'

abbrev DividingLabel (G : PrimeGroups) (g : Fin G.size) (n : ℕ) :=
  {p : Label G g // p.val ∣ n}

abbrev MarkCoordinate (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ)
    (g : Fin G.size) :=
  {f : Fin (t g) → Label G g // Function.Injective f ∧ ∀ j, (f j).val ∣ n}

abbrev MarkTuple (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ) :=
  {z : Tuple G t // admissibleMarks G t n z}

def dividingLabelEquiv (G : PrimeGroups) (g : Fin G.size) (n : ℕ) :
    DividingLabel G g n ≃ {p : ℕ // p ∈ (G.primes g).filter (fun p => p ∣ n)} where
  toFun p := ⟨p.val.val, by
    exact Finset.mem_filter.mpr ⟨p.val.property, p.property⟩⟩
  invFun p := ⟨⟨p.val, (Finset.mem_filter.mp p.property).1⟩,
    (Finset.mem_filter.mp p.property).2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

theorem dividingLabel_card (G : PrimeGroups) (g : Fin G.size) (n : ℕ) :
    Fintype.card (DividingLabel G g n) = omegaGroup G g n := by
  rw [Fintype.card_congr (dividingLabelEquiv G g n), Fintype.card_coe]
  rfl

def markCoordinateEquiv (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ)
    (g : Fin G.size) :
    MarkCoordinate G t n g ≃ (Fin (t g) ↪ DividingLabel G g n) where
  toFun f := ⟨fun j => ⟨f.val j, f.property.2 j⟩, by
    intro a b h
    apply f.property.1
    exact congrArg Subtype.val h⟩
  invFun f := ⟨fun j => (f j).val, ⟨by
    intro a b h
    apply f.injective
    apply Subtype.ext
    exact h, fun j => (f j).property⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    rfl
  right_inv f := by
    ext j
    rfl

theorem markCoordinate_card (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ)
    (g : Fin G.size) :
    Fintype.card (MarkCoordinate G t n g) =
      (omegaGroup G g n).descFactorial (t g) := by
  rw [Fintype.card_congr (markCoordinateEquiv G t n g), Fintype.card_embedding_eq,
    Fintype.card_fin, dividingLabel_card]

def markTupleEquiv (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ) :
    MarkTuple G t n ≃ ((g : Fin G.size) → MarkCoordinate G t n g) where
  toFun z := fun g => ⟨fun j => z.val g j,
    ⟨(z.property g).1, (z.property g).2⟩⟩
  invFun z := ⟨fun g j => (z g).val j, fun g => ⟨(z g).property.1, (z g).property.2⟩⟩
  left_inv z := by
    apply Subtype.ext
    funext g j
    rfl
  right_inv z := by
    funext g
    apply Subtype.ext
    funext j
    rfl

theorem markTuple_card (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ) :
    Fintype.card (MarkTuple G t n) =
      ∏ g, (omegaGroup G g n).descFactorial (t g) := by
  rw [Fintype.card_congr (markTupleEquiv G t n), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro g hg
  exact markCoordinate_card G t n g

theorem mark_indicator_sum (G : PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ) :
    (∑ z : Tuple G t, if admissibleMarks G t n z then (1 : ℂ) else 0) =
      (Fintype.card (MarkTuple G t n) : ℂ) := by
  rw [← Finset.sum_filter (s := Finset.univ) (p := fun z => admissibleMarks G t n z)
    (f := fun _ => (1 : ℂ))]
  simp [MarkTuple, Fintype.card_subtype]

theorem weightedMarks_const_eq_markWeight (G : PrimeGroups) (q : ℝ)
    (t : Fin G.size → ℕ) (n : ℕ) :
    weightedMarks G q t (fun _ => (1 : ℂ)) n = (markWeight G q t n : ℂ) := by
  have hreal :
      (q ^ ((omega G n : ℤ) - ∑ g, (t g : ℤ)) *
        ∏ g, (mass G g)⁻¹ ^ t g) *
        ∏ g, ((omegaGroup G g n).descFactorial (t g) : ℝ) =
      q ^ ((omega G n : ℤ) - ∑ g, (t g : ℤ)) *
        ∏ g, ((omegaGroup G g n).descFactorial (t g) : ℝ) / (mass G g) ^ t g := by
    calc
      _ = q ^ ((omega G n : ℤ) - ∑ g, (t g : ℤ)) *
          ∏ g, ((mass G g)⁻¹ ^ t g *
            ((omegaGroup G g n).descFactorial (t g) : ℝ)) := by
          rw [Finset.prod_mul_distrib]
          ring
      _ = _ := by
          congr 1
          apply Finset.prod_congr rfl
          intro g hg
          rw [inv_pow]
          ring
  unfold weightedMarks markWeight
  rw [mark_indicator_sum, markTuple_card]
  push_cast
  simpa only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_zpow,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_div,
    Complex.ofReal_natCast] using
      congrArg Complex.ofReal hreal

theorem markWeight_log_bound (P : Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ G : PrimeGroups, Admissible P x G → ∀ n : ℕ,
        markWeight G P.q (fun _ => P.ell) n ≤ L x ^ C := by
  obtain ⟨Cm, hCm⟩ := Erdos821.Blueprint.Analytic.mark_sup P P.ell
  let C := max Cm 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := by
    exact Real.tendsto_log_atTop.eventually_ge_atTop 1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCm, hL] with x hxmark hxL
  intro G hG n
  have hraw := hxmark G hG (fun _ => P.ell) (fun _ => (1 : ℂ)) 1
    (by intro g; exact le_rfl) (by norm_num) (by intro z; simp) n
  rw [weightedMarks_const_eq_markWeight] at hraw
  have hmass (g : Fin G.size) : 0 < mass G g :=
    lt_of_lt_of_le P.positive.2.2.1 (hG.2.2.1 g).1
  have hpos : 0 ≤ markWeight G P.q (fun _ => P.ell) n := by
    unfold markWeight
    apply mul_nonneg
    · exact (zpow_pos P.damping.1 _).le
    · apply Finset.prod_nonneg
      intro g hg
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact pow_nonneg (le_of_lt (hmass g)) _
  have hCm_le : Cm ≤ max Cm 0 + 1 := by
    have h := le_max_left Cm 0
    linarith
  have hpow : L x ^ Cm ≤ L x ^ C := by
    apply Real.rpow_le_rpow_of_exponent_le hxL hCm_le
  calc
    markWeight G P.q (fun _ => P.ell) n ≤ L x ^ Cm := by
      simpa [Complex.norm_real, abs_of_nonneg hpos] using hraw
    _ ≤ L x ^ C := hpow

set_option backward.isDefEq.respectTransparency false in
theorem triple_factor_sum (M : ℕ) (hM : M ≠ 0)
    (f : ℕ → ℕ → ℕ → ℂ) :
    (∑ mh ∈ M.divisorsAntidiagonal, ∑ pr ∈ mh.2.divisorsAntidiagonal,
      f mh.1 pr.1 pr.2) =
      ∑ m ∈ Finset.Icc 1 M, ∑ p ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 M,
        if m * p * r = M then f m p r else 0 := by
  let s := M.divisorsAntidiagonal.sigma (fun mh => mh.2.divisorsAntidiagonal)
  let t := (((Finset.Icc 1 M).product (Finset.Icc 1 M)).product
    (Finset.Icc 1 M)).filter (fun mpr => mpr.1.1 * mpr.1.2 * mpr.2 = M)
  calc
    _ = ∑ a ∈ s, f a.1.1 a.2.1 a.2.2 := by rw [Finset.sum_sigma']
    _ = ∑ a ∈ t, f a.1.1 a.1.2 a.2 := by
      apply Finset.sum_bij (fun a _ => ((a.1.1, a.2.1), a.2.2))
      · intro a ha
        obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
        obtain ⟨heq1, _⟩ := Nat.mem_divisorsAntidiagonal.mp ha1
        obtain ⟨heq2, hpos⟩ := Nat.mem_divisorsAntidiagonal.mp ha2
        have hm : 0 < a.1.1 := Nat.pos_of_ne_zero
          (Nat.left_ne_zero_of_mem_divisorsAntidiagonal ha1)
        have hp : 0 < a.2.1 := Nat.pos_of_ne_zero
          (Nat.left_ne_zero_of_mem_divisorsAntidiagonal ha2)
        have hr : 0 < a.2.2 := Nat.pos_of_ne_zero
          (Nat.right_ne_zero_of_mem_divisorsAntidiagonal ha2)
        have heq : a.1.1 * a.2.1 * a.2.2 = M := by
          rw [Nat.mul_assoc, heq2, heq1]
        have hmle : a.1.1 ≤ M := by
          rw [← heq, Nat.mul_assoc]
          exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hp hr)
        have hple : a.2.1 ≤ M := by
          rw [← heq]
          calc
            a.2.1 ≤ a.1.1 * a.2.1 := Nat.le_mul_of_pos_left _ hm
            _ ≤ a.1.1 * a.2.1 * a.2.2 := Nat.le_mul_of_pos_right _ hr
        have hrle : a.2.2 ≤ M := heq ▸ Nat.le_mul_of_pos_left _ (Nat.mul_pos hm hp)
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hm, hmle⟩,
            Finset.mem_Icc.mpr ⟨hp, hple⟩⟩, Finset.mem_Icc.mpr ⟨hr, hrle⟩⟩, heq⟩
      · intro a ha b hb hab
        obtain ⟨_, ha2⟩ := Finset.mem_sigma.mp ha
        obtain ⟨_, hb2⟩ := Finset.mem_sigma.mp hb
        have haeq := (Nat.mem_divisorsAntidiagonal.mp ha2).1
        have hbeq := (Nat.mem_divisorsAntidiagonal.mp hb2).1
        have hm : a.1.1 = b.1.1 := congrArg (fun v => v.1.1) hab
        have hp : a.2.1 = b.2.1 := congrArg (fun v => v.1.2) hab
        have hr : a.2.2 = b.2.2 := congrArg (fun v : (ℕ × ℕ) × ℕ => v.2) hab
        have hh : a.1.2 = b.1.2 := by rw [← haeq, ← hbeq, hp, hr]
        have hfirst : a.1 = b.1 := Prod.ext hm hh
        have hsecond : a.2 = b.2 := Prod.ext hp hr
        exact Sigma.ext hfirst (heq_of_eq hsecond)
      · intro b hb
        obtain ⟨hb0, heq⟩ := Finset.mem_filter.mp hb
        obtain ⟨hbmp, hbr⟩ := Finset.mem_product.mp hb0
        obtain ⟨hbm, hbp⟩ := Finset.mem_product.mp hbmp
        have hp : 0 < b.1.2 := (Finset.mem_Icc.mp hbp).1
        have hr : 0 < b.2 := (Finset.mem_Icc.mp hbr).1
        refine ⟨⟨(b.1.1, b.1.2 * b.2), (b.1.2, b.2)⟩, ?_, rfl⟩
        exact Finset.mem_sigma.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr
          ⟨by simpa [Nat.mul_assoc] using heq, hM⟩,
          Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos hp hr).ne'⟩⟩
      · intro a _
        rfl
    _ = _ := by
      simp only [t, Finset.sum_filter, Finset.product_eq_sprod,
        Finset.sum_product]

theorem groupFreePart_ne_zero (G : PrimeGroups) (n : ℕ) :
    groupFreePart G n ≠ 0 := by
  unfold groupFreePart
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).ne_zero

theorem groupFreePart_dvd (G : PrimeGroups) (n : ℕ) (hn : n ≠ 0) :
    groupFreePart G n ∣ n := by
  calc
    _ ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Finset.prod_dvd_prod_of_subset _ _ (fun p => p ^ n.factorization p)
        Finset.sdiff_subset
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

def endpointFactors (x : ℝ) (F : Endpoint) : List (ℕ → ℂ) :=
  [fun m => F.alpha m * F.chi (m : ZMod F.modulus) * Analytic.mellin m F.sigma₀,
   fun (p : ℕ) => if F.lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ F.hi ∧ rough (W x) p
     then Analytic.mellin p F.sigma₁ else 0,
   F.residual]

theorem endpoint_eq_convList (G : PrimeGroups) (x : ℝ) (F : Endpoint) (n : ℕ) :
    endpoint G x F n = dirichletConvList (endpointFactors x F) (groupFreePart G n) := by
  let M := groupFreePart G n
  let a : ℕ → ℂ := fun m =>
    F.alpha m * F.chi (m : ZMod F.modulus) * Analytic.mellin m F.sigma₀
  let b : ℕ → ℂ := fun p =>
    if F.lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ F.hi ∧ rough (W x) p
      then Analytic.mellin p F.sigma₁ else 0
  let c := F.residual
  have hM : M ≠ 0 := by simpa [M] using groupFreePart_ne_zero G n
  have hsum := triple_factor_sum M hM (fun m p r => a m * b p * c r)
  have hfactor :
      dirichletConvList [a, b, c] M =
        ∑ mh ∈ M.divisorsAntidiagonal,
          ∑ pr ∈ mh.2.divisorsAntidiagonal, a mh.1 * b pr.1 * c pr.2 := by
    change (∑ d ∈ M.divisors, a d *
      ∑ p ∈ (M / d).divisors, b p * c ((M / d) / p)) = _
    calc
      _ = ∑ d ∈ M.divisors, a d *
          ∑ pr ∈ (M / d).divisorsAntidiagonal, b pr.1 * c pr.2 := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [← Nat.sum_divisorsAntidiagonal (fun p r => b p * c r)]
      _ = ∑ mh ∈ M.divisorsAntidiagonal, a mh.1 *
          ∑ pr ∈ mh.2.divisorsAntidiagonal, b pr.1 * c pr.2 := by
            rw [← Nat.sum_divisorsAntidiagonal
              (fun d h => a d * ∑ pr ∈ h.divisorsAntidiagonal, b pr.1 * c pr.2)]
      _ = ∑ mh ∈ M.divisorsAntidiagonal,
          ∑ pr ∈ mh.2.divisorsAntidiagonal, a mh.1 * b pr.1 * c pr.2 := by
            apply Finset.sum_congr rfl
            intro mh hmh
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro pr hpr
            ring
  have hendpoint :
      (∑ m ∈ Finset.Icc 1 M, ∑ p ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 M,
        if m * p * r = M ∧ F.lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ F.hi ∧ rough (W x) p then
          F.alpha m * F.chi (m : ZMod F.modulus) * mellin m F.sigma₀ *
            mellin p F.sigma₁ * F.residual r else 0) =
      ∑ m ∈ Finset.Icc 1 M, ∑ p ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 M,
        if m * p * r = M then a m * b p * c r else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro r hr
    by_cases heq : m * p * r = M
    · by_cases hc : F.lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ F.hi ∧ rough (W x) p
      · simp [heq, hc, a, b, c]
      · simp [heq, hc, a, b, c]
    · simp [heq, a, b, c]
  change (∑ m ∈ Finset.Icc 1 M, ∑ p ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 M,
      if m * p * r = M ∧ F.lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ F.hi ∧ rough (W x) p then
        F.alpha m * F.chi (m : ZMod F.modulus) * Analytic.mellin m F.sigma₀ *
          Analytic.mellin p F.sigma₁ * F.residual r else 0) =
    dirichletConvList [a, b, c] M
  calc
    _ = ∑ m ∈ Finset.Icc 1 M, ∑ p ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 M,
        if m * p * r = M then a m * b p * c r else 0 := hendpoint
    _ = ∑ mh ∈ M.divisorsAntidiagonal,
        ∑ pr ∈ mh.2.divisorsAntidiagonal, a mh.1 * b pr.1 * c pr.2 := hsum.symm
    _ = dirichletConvList [a, b, c] M := hfactor.symm

theorem endpointFactors_bound (x : ℝ) (F : Endpoint) (R : ℝ)
    (hR : 0 ≤ R) (hR1 : 1 ≤ R)
    (hcoef : ∀ n, ‖F.alpha n‖ ≤ R ∧ ‖F.residual n‖ ≤ R) :
    ∀ f ∈ endpointFactors x F, ∀ n, 0 < n → ‖f n‖ ≤ R := by
  intro f hf n hn
  simp only [endpointFactors, List.mem_cons, List.mem_singleton, List.not_mem_nil] at hf
  rcases hf with hf | hf | hf
  · subst f
    have hc : ‖F.chi (n : ZMod F.modulus)‖ ≤ 1 :=
      F.chi.norm_le_one _
    have hm : ‖Analytic.mellin n F.sigma₀‖ = 1 := by
      exact Erdos821.P5Core.norm_mellin _ _
    calc
      ‖F.alpha n * F.chi (n : ZMod F.modulus) * Analytic.mellin n F.sigma₀‖ =
          ‖F.alpha n‖ * ‖F.chi (n : ZMod F.modulus)‖ *
            ‖Analytic.mellin n F.sigma₀‖ := by simp [norm_mul]
      _ ≤ ‖F.alpha n‖ * 1 := by
        rw [hm, mul_one]
        exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ ≤ R := by simpa using (hcoef n).1
  · subst f
    by_cases hp : F.lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ F.hi ∧ rough (W x) n
    · simpa [hp] using hR1
    · simp [hp]
      exact hR
  · rcases hf with hf | hf
    · subst f
      exact (hcoef n).2
    · contradiction

theorem endpoint_norm_bound (x R : ℝ) (G : PrimeGroups) (F : Endpoint)
    (n : ℕ) (hn : 0 < n) (hR : 0 ≤ R) (hR1 : 1 ≤ R)
    (hcoef : ∀ n, ‖F.alpha n‖ ≤ R ∧ ‖F.residual n‖ ≤ R) :
    ‖endpoint G x F n‖ ≤ R ^ 3 * (n.divisors.card : ℝ) ^ 3 := by
  let M := groupFreePart G n
  have hM : M ≠ 0 := by simpa [M] using groupFreePart_ne_zero G n
  have hMdiv : M ∣ n := by
    simpa [M] using groupFreePart_dvd G n hn.ne'
  have hsub : M.divisors ⊆ n.divisors :=
    Nat.divisors_subset_of_dvd hn.ne' hMdiv
  have hcard : M.divisors.card ≤ n.divisors.card := Finset.card_le_card hsub
  have hlist : endpointFactors x F ≠ [] := by simp [endpointFactors]
  have hbound := Erdos821.Classical.dirichletConvList_norm_le R hR
    (endpointFactors x F) hlist (endpointFactors_bound x F R hR hR1 hcoef) M
    (Nat.pos_of_ne_zero hM)
  rw [endpoint_eq_convList]
  calc
    ‖dirichletConvList (endpointFactors x F) M‖ ≤ R ^ (endpointFactors x F).length *
        (M.divisors.card : ℝ) ^ (endpointFactors x F).length := hbound
    _ = R ^ 3 * (M.divisors.card : ℝ) ^ 3 := by
      simp [endpointFactors]
    _ ≤ R ^ 3 * (n.divisors.card : ℝ) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Nat.pow_le_pow_left hcard 3

def momentLogFactor (A : ℝ) : ℝ :=
  max 1 (max ((Real.log 2) ^ A) (3 ^ max A 0))

theorem logMoment_majorant (x Y A : ℝ) (hx : 4 ≤ x) (hL : 3 ≤ L x)
    (hY : 1 ≤ Y) (hYx : Y ≤ x ^ 2) :
    Real.log (2 * Y) ^ A ≤ momentLogFactor A * L x ^ max A 0 := by
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hargpos : 0 < 2 * Y := by positivity
  have hargupper : 2 * Y ≤ 2 * x ^ 2 := by nlinarith
  have hzupper : Real.log (2 * Y) ≤ 3 * L x := by
    change Real.log (2 * Y) ≤ 3 * Real.log x
    have hu := Real.log_le_log hargpos hargupper
    have hx2ne : x ^ 2 ≠ 0 := pow_ne_zero _ hxpos.ne'
    rw [Real.log_mul (by norm_num) hx2ne, Real.log_pow] at hu
    norm_num at hu
    have hLlog : 3 ≤ Real.log x := by simpa [L] using hL
    nlinarith [hlog2le]
  have harglower : 2 ≤ 2 * Y := by nlinarith
  have hzlower : Real.log 2 ≤ Real.log (2 * Y) :=
    Real.log_le_log (by norm_num) harglower
  have hzpos : 0 < Real.log (2 * Y) := hlog2pos.trans_le hzlower
  by_cases hA : 0 ≤ A
  · have hD : max A 0 = A := max_eq_left hA
    have hpow := Real.rpow_le_rpow (x := Real.log (2 * Y))
      (y := 3 * L x) (z := A) (le_of_lt hzpos) hzupper hA
    have hmul : (3 * L x) ^ A = 3 ^ A * L x ^ A :=
      Real.mul_rpow (by norm_num) (le_of_lt hLpos)
    have hK : 3 ^ A ≤ momentLogFactor A := by
      dsimp [momentLogFactor]
      rw [hD]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    calc
      Real.log (2 * Y) ^ A ≤ (3 * L x) ^ A := hpow
      _ = 3 ^ A * L x ^ A := hmul
      _ ≤ momentLogFactor A * L x ^ max A 0 := by
        rw [hD]
        exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (le_of_lt hLpos) A)
  · have hAneg : A < 0 := lt_of_not_ge hA
    have hD : max A 0 = 0 := max_eq_right (le_of_lt hAneg)
    have hinv : (Real.log (2 * Y))⁻¹ ≤ (Real.log 2)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hlog2pos hzlower
    have hpow := Real.rpow_le_rpow (x := (Real.log (2 * Y))⁻¹)
      (y := (Real.log 2)⁻¹) (z := -A) (by positivity) hinv (by linarith)
    have hident (z : ℝ) : z ^ A = z⁻¹ ^ (-A) := by
      calc
        z ^ A = z ^ (-(-A)) := by congr 1 <;> ring
        _ = z⁻¹ ^ (-A) := Real.rpow_neg_eq_inv_rpow z (-A)
    have hK : (Real.log 2) ^ A ≤ momentLogFactor A := by
      dsimp [momentLogFactor]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    calc
      Real.log (2 * Y) ^ A = (Real.log (2 * Y))⁻¹ ^ (-A) := hident _
      _ ≤ (Real.log 2)⁻¹ ^ (-A) := hpow
      _ = (Real.log 2) ^ A := (hident _).symm
      _ ≤ momentLogFactor A := hK
      _ = momentLogFactor A * L x ^ max A 0 := by simp [hD]

theorem markWeight_nonneg (P : Geometry) (G : PrimeGroups) (x : ℝ)
    (hG : Admissible P x G) (n : ℕ) :
    0 ≤ markWeight G P.q (fun _ => P.ell) n := by
  have hmass (g : Fin G.size) : 0 < mass G g :=
    lt_of_lt_of_le P.positive.2.2.1 (hG.2.2.1 g).1
  unfold markWeight
  apply mul_nonneg
  · exact (zpow_pos P.damping.1 _).le
  · apply Finset.prod_nonneg
    intro g hg
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact pow_nonneg (le_of_lt (hmass g)) _

theorem endpointSquareTask_proof : EndpointSquareTask := by
  intro inputs P C hC
  obtain ⟨Cm, hCmpos, hmark⟩ := markWeight_log_bound P
  obtain ⟨Cdiv, Kdiv, hKdiv, hdiv⟩ := inputs.divisors 6
  let D := max Cdiv 0
  let Klog := momentLogFactor Cdiv
  let Ctotal := 6 * C + 2 * Cm + D + 1
  let Ktotal := Kdiv * Klog
  have hD : 0 ≤ D := by dsimp [D]; exact le_max_right _ _
  have hKlog : 0 < Klog := by
    dsimp [Klog, momentLogFactor]
    positivity
  have hCtotal : 0 < Ctotal := by
    dsimp [Ctotal, D]
    positivity
  have hKtotal : 0 < Ktotal := by
    dsimp [Ktotal]
    exact mul_pos hKdiv hKlog
  have hLlarge : ∀ᶠ x : ℝ in atTop, 3 ≤ L x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 3
  have hxlarge : ∀ᶠ x : ℝ in atTop, 4 ≤ x := eventually_ge_atTop 4
  refine ⟨Ctotal, Ktotal, hCtotal, hKtotal, ?_⟩
  filter_upwards [hmark, hLlarge, hxlarge] with x hxmark hxL hx
  intro G F N hG hN hcoeff
  by_cases hNzero : N = 0
  · subst N
    simp [Ktotal, Ctotal]
  · have hNpos : 1 ≤ N := by omega
    have hLpos : 0 < L x := by linarith
    have hLreal : 1 ≤ L x := by linarith
    have hY : 1 ≤ (N : ℝ) := by exact_mod_cast hNpos
    have hYx : (N : ℝ) ≤ x ^ 2 := hN
    have hlog := logMoment_majorant x (N : ℝ) Cdiv hx hxL hY hYx
    have hdivN := (hdiv (N : ℝ) hY).2
    have hmoment :
        (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 6) ≤
          Kdiv * (N : ℝ) * Real.log (2 * (N : ℝ)) ^ Cdiv := by
      simpa using hdivN
    have hRpos : 0 < L x ^ C := Real.rpow_pos_of_pos hLpos C
    have hRnonneg : 0 ≤ L x ^ C := hRpos.le
    have hRone : 1 ≤ L x ^ C :=
      Real.one_le_rpow hLreal (le_of_lt hC)
    have hCmnonneg : 0 ≤ Cm := le_of_lt hCmpos
    have hbase : 0 ≤ 6 * C + 2 * Cm := by positivity
    have htotalExp : 6 * C + 2 * Cm + D ≤ Ctotal := by
      dsimp [Ctotal]
      linarith
    have hpowBase : (L x ^ C) ^ 6 = L x ^ (6 * C) := by
      calc
        (L x ^ C) ^ 6 = (L x ^ C) ^ (6 : ℝ) :=
          (Real.rpow_natCast (L x ^ C) 6).symm
        _ = L x ^ (C * 6) := (Real.rpow_mul (le_of_lt hLpos) C 6).symm
        _ = L x ^ (6 * C) := by rw [mul_comm]
    have hpowMark : (L x ^ Cm) ^ 2 = L x ^ (2 * Cm) := by
      calc
        (L x ^ Cm) ^ 2 = (L x ^ Cm) ^ (2 : ℝ) :=
          (Real.rpow_natCast (L x ^ Cm) 2).symm
        _ = L x ^ (Cm * 2) := (Real.rpow_mul (le_of_lt hLpos) Cm 2).symm
        _ = L x ^ (2 * Cm) := by rw [mul_comm]
    have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
        ‖endpoint G x F n *
          (markWeight G P.q (fun _ => P.ell) n : ℂ)‖ ^ 2 ≤
          L x ^ (6 * C + 2 * Cm) * (n.divisors.card : ℝ) ^ 6 := by
      have hnpos : 0 < n := by
        have h := Finset.mem_Icc.mp hn
        omega
      have hE := endpoint_norm_bound x (L x ^ C) G F n hnpos hRnonneg hRone hcoeff
      have hm := hxmark G hG n
      have hmpos := markWeight_nonneg P G x hG n
      have hmabs : ‖(markWeight G P.q (fun _ => P.ell) n : ℂ)‖ ≤ L x ^ Cm := by
        simpa [Complex.norm_real, abs_of_nonneg hmpos] using hm
      have hnorm :
          ‖endpoint G x F n *
            (markWeight G P.q (fun _ => P.ell) n : ℂ)‖ ≤
            ((L x ^ C) ^ 3 * (n.divisors.card : ℝ) ^ 3) * L x ^ Cm := by
        calc
          _ = ‖endpoint G x F n‖ *
              ‖(markWeight G P.q (fun _ => P.ell) n : ℂ)‖ := norm_mul _ _
          _ ≤ _ := mul_le_mul hE hmabs (norm_nonneg _) (by positivity)
      calc
        _ ≤ (((L x ^ C) ^ 3 * (n.divisors.card : ℝ) ^ 3) * L x ^ Cm) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
        _ = L x ^ (6 * C + 2 * Cm) * (n.divisors.card : ℝ) ^ 6 := by
          calc
            _ = L x ^ (6 * C) * (n.divisors.card : ℝ) ^ 6 * L x ^ (2 * Cm) := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, hpowBase, hpowMark]
            _ = (L x ^ (6 * C) * L x ^ (2 * Cm)) *
                (n.divisors.card : ℝ) ^ 6 := by ring
            _ = L x ^ (6 * C + 2 * Cm) *
                (n.divisors.card : ℝ) ^ 6 := by
              rw [← Real.rpow_add hLpos]
    have hsum :
        (∑ n ∈ Finset.Icc 1 N,
          ‖endpoint G x F n *
            (markWeight G P.q (fun _ => P.ell) n : ℂ)‖ ^ 2) ≤
          L x ^ (6 * C + 2 * Cm) *
            (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 6) := by
      calc
        _ ≤ ∑ n ∈ Finset.Icc 1 N,
            L x ^ (6 * C + 2 * Cm) * (n.divisors.card : ℝ) ^ 6 := by
          apply Finset.sum_le_sum
          intro n hn
          exact hpoint n hn
        _ = _ := by rw [← Finset.mul_sum]
    have hfinal0 :
        L x ^ (6 * C + 2 * Cm) *
            (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 6) ≤
          Ktotal * (N : ℝ) * L x ^ (6 * C + 2 * Cm + D) := by
      calc
        _ ≤ L x ^ (6 * C + 2 * Cm) *
            (Kdiv * (N : ℝ) * Real.log (2 * (N : ℝ)) ^ Cdiv) :=
          mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg (le_of_lt hLpos) _)
        _ ≤ Kdiv * Klog * (N : ℝ) *
            L x ^ (6 * C + 2 * Cm + D) := by
          have hmul := mul_le_mul_of_nonneg_left hlog
            (by positivity : 0 ≤ Kdiv * (N : ℝ) * L x ^ (6 * C + 2 * Cm))
          calc
            _ = (Kdiv * (N : ℝ) * L x ^ (6 * C + 2 * Cm)) *
                Real.log (2 * (N : ℝ)) ^ Cdiv := by ring
            _ ≤ (Kdiv * (N : ℝ) * L x ^ (6 * C + 2 * Cm)) *
                (Klog * L x ^ D) := hmul
            _ = Kdiv * Klog * (N : ℝ) *
                L x ^ (6 * C + 2 * Cm + D) := by
                  calc
                    _ = Kdiv * Klog * (N : ℝ) *
                        (L x ^ (6 * C + 2 * Cm) * L x ^ D) := by ring
                    _ = Kdiv * Klog * (N : ℝ) *
                        L x ^ (6 * C + 2 * Cm + D) := by
                          rw [← Real.rpow_add hLpos]
    have hfinal :
        (∑ n ∈ Finset.Icc 1 N,
          ‖endpoint G x F n *
            (markWeight G P.q (fun _ => P.ell) n : ℂ)‖ ^ 2) ≤
          Ktotal * N * L x ^ Ctotal := by
      calc
        _ ≤ Ktotal * (N : ℝ) * L x ^ (6 * C + 2 * Cm + D) :=
          hsum.trans hfinal0
        _ ≤ Ktotal * (N : ℝ) * L x ^ Ctotal := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hLreal htotalExp
    simpa using hfinal

end Erdos821.P6Sq

