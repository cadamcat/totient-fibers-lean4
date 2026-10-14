import Erdos821.Supply

/-! Concrete, proof-safe definitions for §§5–6. No planning theorem is imported. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace Erdos821.S56

attribute [local instance] Classical.propDecidable

def L (x : ℝ) : ℝ := Real.log x

def T (x : ℝ) : ℝ := Real.log (L x)

def W (x : ℝ) : ℝ := Real.exp (Real.sqrt (L x))

def N (u : ℕ) : ℕ := 2 * u + 1

def Rough (y : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → y < (p : ℝ)

def Smooth (y : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ y

def τ (n : ℕ) : ℝ := n.divisors.card

def ω (P : Finset ℕ) (n : ℕ) : ℕ := (P.filter (· ∣ n)).card

def natCell (a b : ℝ) : Finset ℕ :=
  (Finset.range (⌊b⌋₊ + 1)).filter fun n => a < (n : ℝ) ∧ (n : ℝ) ≤ b

def dyad (U : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * U⌋₊ + 1)).filter fun n => U ≤ (n : ℝ) ∧ (n : ℝ) < 2 * U

def primesLE (y : ℝ) : Finset ℕ := (natCell 0 y).filter Nat.Prime

def V (y : ℝ) : ℝ := ∏ p ∈ primesLE y, (1 - 1 / (p : ℝ))

def V₁ (y : ℝ) : ℝ := ∏ p ∈ (primesLE y).filter (3 ≤ ·), (1 - 1 / ((p : ℝ) - 1))

def singularSeries : ℝ :=
  2 * ∏' p : ℕ, if p.Prime ∧ 3 ≤ p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

def Li (y : ℝ) : ℝ := ∫ t in 2..y, 1 / Real.log t

def twist (t : ℝ) (n : ℕ) : ℂ := Complex.exp (Complex.I * (t * Real.log n : ℝ))

def indicator (P : ℕ → Prop) (m : ℕ) : ℝ := if P m then 1 else 0

def harmonic (f : ℕ → ℝ) : ℝ := ∑' n : ℕ, f n / (n : ℝ)

def restricted (a : ℕ → ℂ) (K : Finset ℕ) (n : ℕ) : ℂ := if n ∈ K then a n else 0

def Discrepancy (x B : ℝ) (a : ℕ → ℂ) : Prop :=
  ∀ r : ℕ, 0 < r → (r : ℝ) ≤ (L x) ^ B →
    ∀ χ : DirichletCharacter ℂ r, ∀ t : ℝ, |t| ≤ (L x) ^ B →
    ∀ a₀ b₀ : ℝ, 1 ≤ a₀ → a₀ ≤ b₀ → b₀ ≤ x ^ (2 : ℕ) →
      ‖∑ m ∈ Finset.Icc ⌈a₀⌉₊ ⌊b₀⌋₊, a m * χ (m : ZMod r) * twist t m / (m : ℂ)‖
        ≤ (L x) ^ (-B)

/- §1 inputs actually used by §§5–6. -/

def primitiveMean (r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  if hr : 0 < r then
    letI : NeZero r := ⟨hr.ne'⟩
    (r : ℝ) / (r.totient : ℝ) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (·.IsPrimitive),
        ‖∑ n ∈ s, a n * χ (n : ZMod r)‖ ^ (2 : ℕ)
  else 0

def factorConvolution (b : ℕ) (a : Fin b → ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ f : Fin b → Fin (n + 1),
    if (∀ i, 0 < (f i).val) ∧ ∏ i, (f i).val = n then ∏ i, a i (f i).val else 0

def fourierPhase {b : ℕ} (ξ t : Fin b → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ i, ξ i * t i) : ℝ))

def fourierHat {b : ℕ} (F : (Fin b → ℝ) → ℂ) (ξ : Fin b → ℝ) : ℂ :=
  ∫ t, F t * fourierPhase (fun i => -ξ i) t

structure SieveProblem (Ω : Type*) where
  objects : Finset Ω
  weight : Ω → ℝ
  primes : Finset ℕ
  bad : ℕ → Ω → Prop
  base : ℝ
  density : ℕ → ℝ

def sieveMass {Ω : Type*} (S : SieveProblem Ω) : ℝ :=
  ∑ o ∈ S.objects.filter (fun o => ∀ p ∈ S.primes, ¬S.bad p o), S.weight o

def sieveRemainder {Ω : Type*} (S : SieveProblem Ω) (d : ℕ) : ℝ :=
  (∑ o ∈ S.objects.filter (fun o => ∀ p ∈ d.primeFactors, S.bad p o), S.weight o) -
    S.base * ∏ p ∈ d.primeFactors, S.density p

def sieveProduct {Ω : Type*} (S : SieveProblem Ω) : ℝ := ∏ p ∈ S.primes, (1 - S.density p)

def SieveHypotheses {Ω : Type*} (S : SieveProblem Ω) (z η C : ℝ) : Prop :=
  1 < z ∧ 0 < η ∧ 0 ≤ C ∧ 0 ≤ S.base ∧ (∀ o ∈ S.objects, 0 ≤ S.weight o) ∧
  (∀ p ∈ S.primes, p.Prime ∧ (p : ℝ) ≤ z ∧ 0 ≤ S.density p ∧ S.density p ≤ 1 - η) ∧
  ∀ w : ℝ, 1 < w → (∑ p ∈ S.primes.filter (fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ (2 : ℕ)),
    S.density p) ≤ C

def sieveErrors {Ω : Type*} (S : SieveProblem Ω) (D : ℝ) : ℝ :=
  ∑ d ∈ (natCell 0 D).filter (fun d => Squarefree d ∧ d.primeFactors ⊆ S.primes),
    |sieveRemainder S d|

def evalSieveCoeff {Ω : Type*} (S : SieveProblem Ω) (coeff : Finset ℕ → ℝ) (o : Ω) : ℝ :=
  ∑ A ∈ S.primes.powerset, coeff A * if ∀ p ∈ A, S.bad p o then 1 else 0

def sievePolynomial (z : ℝ) (h : ℕ) (coeff : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ (natCell 0 (z ^ (4 * h + 2))).filter (· ∣ n), coeff d

structure Geometry where
  q : ℝ
  ell : ℕ
  r₀ : ℕ
  jExceptional : ℕ
  slotExceptional : ℕ
  c₁ : ℝ
  c₂ : ℝ
  s' : ℝ
  ratio : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  vMinus : ℝ
  vPlus : ℝ
  cMinus : ℝ
  cPlus : ℝ
  groupMinus : ℝ
  groupPlus : ℝ
  jMax : ℝ → ℕ
  groups : ℝ → Finset ℕ
  P : ℝ → ℕ → Finset ℕ
  big : ℝ → ℕ → Bool

def bandScale (G : Geometry) (x : ℝ) (j : ℕ) : ℝ := G.s' * L x * G.ratio ^ (-(j : ℝ))

def Q (G : Geometry) (x : ℝ) (j : ℕ) : Finset ℕ :=
  (primesLE (Real.exp (G.c₂ * bandScale G x j))).filter fun p =>
    G.c₁ * bandScale G x j ≤ Real.log p

def groupMass (G : Geometry) (x : ℝ) (g : ℕ) : ℝ :=
  ∑ p ∈ G.P x g, 1 / (p : ℝ)

def allP (G : Geometry) (x : ℝ) : Finset ℕ := (G.groups x).biUnion (G.P x)

def groupPart (G : Geometry) (x : ℝ) (n : ℕ) : ℕ :=
  ∏ p ∈ allP G x, p ^ n.factorization p

def outsidePart (G : Geometry) (x : ℝ) (n : ℕ) : ℕ := n / groupPart G x n

def markedWeight (G : Geometry) (x : ℝ) (n : ℕ) : ℝ :=
  ∏ g ∈ G.groups x,
    G.q ^ ((ω (G.P x g) n : ℝ) - (G.ell : ℝ)) *
      ((ω (G.P x g) n).descFactorial G.ell : ℝ) / groupMass G x g ^ G.ell

abbrev Slots (G : Geometry) (x : ℝ) := Fin (G.jMax x + 1) × Fin G.r₀

def exceptional (G : Geometry) {x : ℝ} (i : Slots G x) : Prop :=
  i.1.val = G.jExceptional ∧ i.2.val = G.slotExceptional

def admissibleSlot (G : Geometry) (x : ℝ) (i : Slots G x) (n : ℕ) : Prop :=
  if exceptional G i then
    Real.exp (G.c₁ * bandScale G x i.1) ≤ (n : ℝ) ∧
    (n : ℝ) ≤ Real.exp (G.c₂ * bandScale G x i.1) ∧ Rough (W x) n
  else n ∈ Q G x i.1

def slotLists (G : Geometry) (x : ℝ) (n : ℕ) : Finset (Slots G x → Fin (n + 1)) :=
  Finset.univ.filter fun f =>
    (∀ i, admissibleSlot G x i (f i).val) ∧ ∏ i, (f i).val = n

def aQ (G : Geometry) (x : ℝ) (n : ℕ) : ℝ :=
  (slotLists G x n).card / ((G.r₀.factorial : ℝ) ^ (G.jMax x + 1))

def candidate (G : Geometry) (x : ℝ) (u : ℕ) : ℝ :=
  aQ G x (outsidePart G x u) * markedWeight G x u

def X_A (G : Geometry) (Ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ u ∈ natCell 0 (2 * x), candidate G x u * Ψ ((u : ℝ) / x)

def H_Q (G : Geometry) (x : ℝ) : ℝ := harmonic (aQ G x)

def H_P (G : Geometry) (x : ℝ) : ℝ :=
  harmonic fun r => if 0 < r ∧ outsidePart G x r = 1 then markedWeight G x r else 0

def ValidGeometry (G : Geometry) : Prop :=
  0 < G.q ∧ G.q < 1 ∧ 1 ≤ G.ell ∧ 1 ≤ G.r₀ ∧ G.slotExceptional < G.r₀ ∧
  0 < G.c₁ ∧ G.c₁ < G.c₂ ∧ 0 < G.s' ∧ 1 < G.ratio ∧ G.c₂ * G.s' < 1 / 4 ∧
  0 < G.a ∧ G.a < G.b ∧ G.b < G.c ∧ G.c < G.d ∧ G.d < 0.47 ∧
  0 < G.vMinus ∧ G.vMinus ≤ G.vPlus ∧ 0 < G.cMinus ∧ G.cMinus ≤ G.cPlus ∧
  0 < G.groupMinus ∧ G.groupMinus ≤ G.groupPlus ∧
  ((G.r₀ : ℝ) - 1) * G.c₁ / G.ratio ≥ G.c₂ + 1 ∧
  ∀ᶠ x : ℝ in atTop,
    G.jExceptional ≤ G.jMax x ∧
    G.cMinus * T x ≤ bandScale G x (G.jMax x) ∧
    bandScale G x (G.jMax x) ≤ G.cPlus * T x ∧
    (∀ g ∈ G.groups x, G.vMinus ≤ groupMass G x g ∧ groupMass G x g ≤ G.vPlus) ∧
    (∀ g ∈ G.groups x, ∀ p ∈ G.P x g, p.Prime ∧
      (if G.big x g then (L x) ^ G.c ≤ Real.log p ∧ Real.log p ≤ (L x) ^ G.d
       else (L x) ^ G.a ≤ Real.log p ∧ Real.log p ≤ (L x) ^ G.b)) ∧
    (∀ g ∈ G.groups x, G.big x g = true → ∃ A B : ℝ,
      1 < A ∧ A < B ∧ G.P x g = (natCell A B).filter Nat.Prime) ∧
    (∀ g ∈ G.groups x, ∀ h ∈ G.groups x, g ≠ h → Disjoint (G.P x g) (G.P x h)) ∧
    (∀ j ≤ G.jMax x, Disjoint (Q G x j) (allP G x)) ∧
    (∀ j ≤ G.jMax x, ∀ k ≤ G.jMax x, j ≠ k → Disjoint (Q G x j) (Q G x k)) ∧
    (∀ b : Bool, G.groupMinus * T x ≤ ((G.groups x).filter (G.big x · = b)).card ∧
      (((G.groups x).filter (G.big x · = b)).card : ℝ) ≤ G.groupPlus * T x)

def Cutoff (Ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ Ψ ∧ ∃ a b : ℝ, 0 < a ∧ a < b ∧ Function.support Ψ ⊆ Set.Icc a b

def PositiveCutoff (Ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ Ψ ∧ (∀ t, 0 ≤ Ψ t) ∧ Function.support Ψ ⊆ Set.Icc 1 2 ∧
    ∃ a b c : ℝ, 1 < a ∧ a < b ∧ b < 2 ∧ 0 < c ∧ ∀ t ∈ Set.Icc a b, c ≤ Ψ t

def typeIISum (G : Geometry) (Ψ : ℝ → ℝ) (x U V' : ℝ) (α β : ℕ → ℂ) : ℂ :=
  ∑ m ∈ dyad U, ∑ n ∈ dyad V',
    if Odd (m * n) ∧ 1 < m * n then
      let u := (m * n - 1) / 2
      (candidate G x u * Ψ ((u : ℝ) / x) : ℝ) * α m * β n
    else 0

def TypeIIEstimate (G : Geometry) (Ψ : ℝ → ℝ) (b D C Cuv : ℝ) : Prop :=
  ∃ B C₀ : ℝ, 0 < B ∧ 0 < C₀ ∧ ∀ᶠ x : ℝ in atTop,
    ∀ U V' : ℝ, x ^ b ≤ U → U ≤ x ^ (1 - b) → x ^ b ≤ V' → V' ≤ x ^ (1 - b) →
    x / Cuv ≤ U * V' → U * V' ≤ Cuv * x → ∀ α β : ℕ → ℂ,
    (∀ m, ‖α m‖ ≤ (L x) ^ C ∧ (α m ≠ 0 → Rough (W x) m)) →
    (∀ n, ‖β n‖ ≤ (L x) ^ C) → Discrepancy x B (restricted α (dyad U)) →
    ‖typeIISum G Ψ x U V' α β‖ ≤ C₀ * x * (L x) ^ (-D)

/- §5 theorem and its independent arithmetic leaves. -/

def residual {n : ℕ} (target : ℝ) (v : Fin n → ℝ) (δ : Fin n → Bool) (i : ℕ) : ℝ :=
  target - ∑ t ∈ Finset.univ.filter (fun t : Fin n => t.val < i), if δ t then v t else 0

def branchMass {n : ℕ} (target : ℝ) (v s : Fin n → ℝ) (γ : ℝ → ℝ) (δ : Fin n → Bool) : ℝ :=
  ∏ i, if δ i then γ ((residual target v δ i.val - v i) / s i)
    else 1 - γ ((residual target v δ i.val - v i) / s i)

def takeTransition (ρ γ : ℝ → ℝ) (t : ℝ) : ℝ := ρ t * γ t

def skipTransition (ρ γ : ℝ → ℝ) (t : ℝ) : ℝ := ρ t * (1 - γ t)

def slotFrequency {n : ℕ} (s ξ : Fin n → ℝ) (δ : Fin n → Bool) (t : Fin n) : ℝ :=
  -ξ t / s t - (if δ t then 1 else 0) *
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => t.val < i.val), ξ i / s i

def roughConvolution (G : Geometry) (x σ : ℝ) (c : ℕ → ℂ) (t : ℕ) : ℂ :=
  ∑ pr ∈ t.divisorsAntidiagonal,
    if Real.exp (G.c₁ * bandScale G x G.jExceptional) ≤ (pr.1 : ℝ) ∧
      (pr.1 : ℝ) ≤ Real.exp (G.c₂ * bandScale G x G.jExceptional) ∧ Rough (W x) pr.1
    then twist σ pr.1 * c pr.2 else 0

def hCoefficient (G : Geometry) (x ρ σ : ℝ) (c : ℕ → ℂ) (h : ℕ) : ℂ :=
  twist ρ h * (markedWeight G x h : ℂ) * roughConvolution G x σ c (outsidePart G x h)

def separatedB (eMin eMax U V' : ℝ) (ae ah α β : ℕ → ℂ) : ℂ :=
  ∑ e ∈ Finset.Icc ⌈eMin⌉₊ ⌊eMax⌋₊, ∑ n ∈ dyad V', ae e * β n *
    ∑ m ∈ dyad U, if 0 < e ∧ 1 < m * n ∧ 2 * e ∣ m * n - 1 then
      α m * ah ((m * n - 1) / (2 * e)) else 0

def pulledE (m m' k : ℝ) : ℝ := (m' - m) / (2 * k)

def pulledN (m m' z k : ℝ) : ℝ := (m' - m) * z / (k * m * m') + 1 / m

def endpointCore (G : Geometry) (x ρ σ : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (α c : ℕ → ℂ) (v : ℕ) : ℂ :=
  ∑ mh ∈ (outsidePart G x v).divisorsAntidiagonal,
    α mh.1 * χ (mh.1 : ZMod r) * twist ρ mh.1 *
      roughConvolution G x (-σ) (fun n => star (c n)) mh.2

def firstEndpoint (G : Geometry) (x ρ σ ξ₂ : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (α c : ℕ → ℂ) : ℕ → ℂ := endpointCore G x (ρ - ξ₂) σ r χ α c

def secondEndpoint (G : Geometry) (x ρ σ ξ₁ : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (α c : ℕ → ℂ) : ℕ → ℂ := endpointCore G x (ξ₁ + ρ) σ r χ α c

def candidateS' (r₀ : ℕ) : ℝ := 1 / ((r₀ : ℝ) * (1 + 6 / 5))

def candidateJMax (r₀ : ℕ) (x : ℝ) : ℕ :=
  ⌊Real.log (candidateS' r₀ * L x / (20 * T x)) / Real.log 2⌋₊

def candidateBandScale (r₀ : ℕ) (x : ℝ) (j : ℕ) : ℝ := candidateS' r₀ * L x * (2 : ℝ) ^ (-(j : ℝ))

def isPBand (r₀ : ℕ) (x : ℝ) (j : ℕ) : Prop :=
  ((L x) ^ (1 / 10 : ℝ) ≤ (3 / 2 : ℝ) * candidateBandScale r₀ x j ∧
    (9 / 5 : ℝ) * candidateBandScale r₀ x j ≤ (L x) ^ (1 / 5 : ℝ)) ∨
  ((L x) ^ (3 / 10 : ℝ) ≤ (3 / 2 : ℝ) * candidateBandScale r₀ x j ∧
    (9 / 5 : ℝ) * candidateBandScale r₀ x j ≤ (L x) ^ (2 / 5 : ℝ))

def candidateGeometry (r₀ jExceptional : ℕ) : Geometry where
  q := 1 / 2
  ell := 1
  r₀ := r₀
  jExceptional := jExceptional
  slotExceptional := 0
  c₁ := 1
  c₂ := 6 / 5
  s' := candidateS' r₀
  ratio := 2
  a := 1 / 10
  b := 1 / 5
  c := 3 / 10
  d := 2 / 5
  vMinus := Real.log (6 / 5) / 2
  vPlus := 2 * Real.log (6 / 5)
  cMinus := 20
  cPlus := 40
  groupMinus := 1 / (40 * Real.log 2)
  groupPlus := 1 / Real.log 2
  jMax := candidateJMax r₀
  groups := fun x => (Finset.range (candidateJMax r₀ x + 1)).filter (isPBand r₀ x)
  P := fun x j => (primesLE (Real.exp ((9 / 5 : ℝ) * candidateBandScale r₀ x j))).filter
    fun p => (3 / 2 : ℝ) * candidateBandScale r₀ x j ≤ Real.log p
  big := fun x j => decide ((L x) ^ (3 / 10 : ℝ) ≤ (3 / 2 : ℝ) * candidateBandScale r₀ x j)

def CandidateGeometryCondition (δ : ℝ) (r₀ : ℕ) : Prop :=
  1 ≤ r₀ ∧ (6 / 5 : ℝ) * candidateS' r₀ < δ ∧ ((r₀ : ℝ) - 1) / 2 ≥ 6 / 5 + 1

def groupEuler (P : Finset ℕ) (q : ℝ) : ℝ := ∏ p ∈ P, (1 + q / ((p : ℝ) - 1))

def markedEuler (P : Finset ℕ) (q : ℝ) : ℝ :=
  groupEuler P q * (∑ p ∈ P, 1 / ((p : ℝ) - 1 + q)) / (∑ p ∈ P, 1 / (p : ℝ))

def remainder (G : Geometry) (Ψ : ℝ → ℝ) (x : ℝ) (d : ℕ) : ℝ :=
  (∑ u ∈ natCell 0 (2 * x), if d ∣ N u then candidate G x u * Ψ ((u : ℝ) / x) else 0) -
    X_A G Ψ x / (d.totient : ℝ)

def TypeIEstimate (G : Geometry) (Ψ : ℝ → ℝ) : Prop :=
  ∀ ϑ D : ℝ, ϑ < 1 / 2 → 0 < D → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    (∑ d ∈ (natCell 0 (x ^ ϑ)).filter (fun d => Odd d ∧ Squarefree d), |remainder G Ψ x d|) ≤
      C * (x * (L x) ^ (-D) + X_A G Ψ x * (L x) ^ (-18 : ℝ))

def weightedMass (G : Geometry) (Ψ : ℝ → ℝ) (x : ℝ) (P : ℕ → Prop) : ℝ :=
  ∑ u ∈ (natCell 0 (2 * x)).filter fun u => P (N u), candidate G x u * Ψ ((u : ℝ) / x)

def cellWidth (x S : ℝ) : ℝ := (L x) ^ (-S)

def logCellIndex (x S : ℝ) (m : ℕ) : ℤ := ⌈Real.log m / cellWidth x S⌉ - 1

def cellLower (x S : ℝ) (i : ℤ) : ℝ := Real.exp ((i : ℝ) * cellWidth x S)

def logCell (x S : ℝ) (i : ℤ) : Finset ℕ :=
  natCell (cellLower x S i) (Real.exp (cellWidth x S) * cellLower x S i)

def cellCoefficient (x S : ℝ) (I : ℕ → Prop) (i : ℤ) : ℝ :=
  ((logCell x S i).filter I).card / (((logCell x S i).filter (Rough (W x))).card : ℝ)

def proxy (x S : ℝ) (I : ℕ → Prop) (m : ℕ) : ℝ :=
  cellCoefficient x S I (logCellIndex x S m) * indicator (Rough (W x)) m

def Test (x b₁ : ℝ) (I : ℕ → Prop) : Prop :=
  I = Nat.Prime ∨ ∃ γ : ℝ, b₁ ≤ γ ∧ γ < 1 / 2 ∧ I = Rough (x ^ γ)

def AmbientCell (x S b₁ : ℝ) (i : ℤ) : Prop :=
  ∃ m ∈ logCell x S i, x ^ (b₁ / 4) ≤ (m : ℝ) ∧ (m : ℝ) ≤ x ^ (1 - b₁ / 4)

def densityDomain (γ w : ℝ) (k : ℕ) : Set (Fin k → ℝ) :=
  {t | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}

def densityTerm (γ w : ℝ) (k : ℕ) : ℝ :=
  (∫ t in densityDomain γ w k, (1 / (w - ∑ i, t i)) * ∏ i, 1 / t i) /
    ((k + 1).factorial : ℝ)

def roughDensity (γ w : ℝ) : ℝ :=
  if 0 < γ ∧ γ ≤ w then 1 / w + ∑ k ∈ Finset.Icc 1 ⌊w / γ⌋₊, densityTerm γ w k else 0

def unbalancedBin (G : Geometry) (Ψ : ℝ → ℝ) (x γ γ' : ℝ) : ℝ :=
  ∑ u ∈ natCell 0 (2 * x), candidate G x u * Ψ ((u : ℝ) / x) *
    (∑ p ∈ (N u).divisors,
      if p.Prime ∧ x ^ γ < (p : ℝ) ∧ (p : ℝ) ≤ x ^ γ' ∧ Rough (x ^ γ) (N u / p) then (1 : ℝ) else 0)

def ν (p : ℕ) (belowW banned : Bool) : ℕ :=
  (if belowW then 2 * p - 1 else 0) + (if banned then p - 1 else 0)

def pairDensity (p : ℕ) (belowW banned : Bool) : ℝ := ν p belowW banned / (p : ℝ) ^ (2 : ℕ)

def slotValues (G : Geometry) (x : ℝ) (i : Slots G x) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.exp (G.c₂ * bandScale G x i.1)⌋₊).filter (admissibleSlot G x i)

abbrev MicroSlots (G : Geometry) (x : ℝ) (j' : ℕ) := {i : Slots G x // j' ≤ i.1.val}

abbrev PGroup (G : Geometry) (x : ℝ) := {g : ℕ // g ∈ G.groups x}

abbrev Assignment (G : Geometry) (x : ℝ) (j' : ℕ) :=
  (∀ i : MicroSlots G x j', {v : ℕ // v ∈ slotValues G x i.val}) ×
  (∀ g : PGroup G x, {p : ℕ // p ∈ G.P x g.val})

def assignmentProduct (G : Geometry) (x : ℝ) (j' : ℕ) (a : Assignment G x j') : ℕ :=
  (∏ i, (a.1 i).val) * ∏ g, (a.2 g).val

def assignmentWeight (G : Geometry) (x : ℝ) (j' : ℕ) : ℝ :=
  ((G.r₀.factorial : ℝ) ^ (G.jMax x + 1 - j'))⁻¹ * ∏ g ∈ G.groups x, (groupMass G x g)⁻¹

def microH_Q (G : Geometry) (x : ℝ) (j' : ℕ) : ℝ :=
  ((G.r₀.factorial : ℝ) ^ (G.jMax x + 1 - j'))⁻¹ *
    ∏ i : MicroSlots G x j', ∑ v ∈ slotValues G x i.val, (v : ℝ)⁻¹

def maskAverage (G : Geometry) (x θ : ℝ) (D u : ℕ) : ℝ :=
  let P := allP G x \ D.primeFactors
  ∑ A ∈ P.powerset, G.q ^ A.card * (1 - G.q) ^ (P.card - A.card) *
    if ∀ p ∈ (primesLE (x ^ θ)).filter (fun p => 3 ≤ p ∧ ¬p ∣ D),
      (p ∉ allP G x ∨ p ∉ A) → ¬p ∣ u then 1 else 0

def pairSieveProduct (z W' : ℝ) (D : ℕ) (P A : Finset ℕ) : ℝ :=
  ∏ p ∈ (primesLE z).filter (fun p => 3 ≤ p ∧ ¬p ∣ D),
    (1 - pairDensity p (decide ((p : ℝ) ≤ W')) (decide (p ∉ P ∨ p ∉ A)))

def balancedMass (G : Geometry) (Ψ : ℝ → ℝ) (x κ : ℝ) : ℝ :=
  weightedMass G Ψ x fun n => 1 < n ∧ ¬n.Prime ∧ Rough (x ^ (1 / 2 - κ)) n

def balancedDyad (G : Geometry) (Ψ : ℝ → ℝ) (x M₁ M₂ : ℝ) : ℝ :=
  ∑ m ∈ dyad M₁, ∑ n ∈ dyad M₂,
    if Rough (W x) m ∧ Rough (W x) n ∧ Odd (m * n) ∧ 1 < m * n then
      let u := (m * n - 1) / 2
      candidate G x u * Ψ ((u : ℝ) / x)
    else 0


end Erdos821.S56
