import Erdos821.Blueprint.Sieve
import Erdos821.Blueprint.Candidate

/-! P8: full-cell matching and ordinary rough-integer densities, independent of Type II. -/
noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint
open Analytic

inductive FactorTest where
  | prime
  | rough (gamma : ℝ)

def test (I : FactorTest) (x : ℝ) (n : ℕ) : ℝ :=
  match I with
  | .prime => if n.Prime then 1 else 0
  | .rough gamma => if rough (x ^ gamma) n then 1 else 0

def logCell (x S : ℝ) (n : ℕ) : Finset ℕ :=
  let delta := L x ^ (-S)
  let j : ℤ := ⌈Real.log n / delta⌉ - 1
  Finset.Ioc ⌊Real.exp ((j : ℝ) * delta)⌋₊ ⌊Real.exp (((j : ℝ) + 1) * delta)⌋₊

def proxyDenominator (x S : ℝ) (n : ℕ) : ℕ :=
  ((logCell x S n).filter (rough (W x))).card

def proxyConstant (I : FactorTest) (x S : ℝ) (n : ℕ) : ℝ :=
  (∑ m ∈ logCell x S n, test I x m) / proxyDenominator x S n

def proxy (I : FactorTest) (x S : ℝ) (n : ℕ) : ℝ :=
  if rough (W x) n then proxyConstant I x S n else 0

def proxyDifference (I : FactorTest) (x S lo hi : ℝ) : ℕ → ℂ :=
  fun n => if lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi then
    ((test I x n - proxy I x S n : ℝ) : ℂ) else 0

def TestAllowed (b kappa : ℝ) (I : FactorTest) : Prop :=
  match I with
  | .prime => True
  | .rough gamma => b ≤ gamma ∧ gamma ≤ 1 / 2 - kappa

def ProxyDiscrepancy : Prop :=
  ∀ b kappa B : ℝ, 0 < b → 0 < kappa → kappa < 1 / 50 → 0 < B →
    ∀ S : ℝ, 2 * B + 3 < S → ∀ᶠ x : ℝ in atTop,
      ∀ (I : FactorTest) (lo hi : ℝ), TestAllowed b kappa I →
        x ^ (b / 4) ≤ lo → lo ≤ hi → hi ≤ x ^ (1 - b / 4) →
        discrepancy x B (proxyDifference I x S lo hi) ∧
        (∀ n : ℕ, lo ≤ (n : ℝ) → (n : ℝ) ≤ hi →
          0 < proxyDenominator x S n ∧ 0 ≤ proxy I x S n ∧ proxy I x S n ≤ 1)

/-- eq:rough-density-definition, with finite Pi-volume for every simplex term. -/
def densityTerm (gamma w : ℝ) (l : ℕ) : ℝ :=
  ∫ t : Fin (l - 1) → ℝ,
    if (∀ i, gamma ≤ t i) ∧ (∑ i, t i) ≤ w - gamma then
      (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹
    else 0

def roughDensity (gamma w : ℝ) : ℝ :=
  w⁻¹ + ∑ l ∈ Finset.Icc 2 ⌊w / gamma⌋₊, densityTerm gamma w l / (l.factorial : ℝ)

def singularSeries : ℝ :=
  2 * ∏' p : Nat.Primes, if p.val = 2 then 1 else 1 - (((p.val : ℝ) - 1)⁻¹) ^ 2

def SieveProducts : Prop :=
  0 < singularSeries ∧
  Tendsto (fun y : ℝ => shiftedSieveProduct y / sieveProduct y) atTop (nhds singularSeries)

def DensityIdentities : Prop :=
  ContinuousOn (fun v : ℝ × ℝ => roughDensity v.1 v.2) {v | 0 < v.1 ∧ v.1 < v.2} ∧
  (∀ b : ℝ, 0 < b → b < 1 / 2 →
    (∫ a : ℝ in b..(1 / 2 : ℝ), roughDensity a (1 - a) / a) = roughDensity b 1 - 1) ∧
  (∃ c K b₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ →
    roughDensity b 1 ≤ Real.exp (-Real.eulerMascheroniConstant) / b *
      (1 + K * Real.exp (-c / b)))

def ProxyDensities : Prop :=
  (∃ K : ℝ, 0 < K ∧ ∀ kappa S : ℝ, 0 < kappa → kappa < 1 / 50 → 0 < S →
    ∀ᶠ x : ℝ in atTop, ∀ m : ℕ,
      x ^ (1 / 2 - 2 * kappa) ≤ (m : ℝ) → (m : ℝ) ≤ x ^ (1 / 2 + 2 * kappa) →
      proxyConstant .prime x S m ≤ K / (L x * sieveProduct (W x))) ∧
  (∀ b kappa S gamma gamma' eps : ℝ, 0 < b → 0 < kappa → kappa < 1 / 50 →
    0 < S → b ≤ gamma → gamma < gamma' → gamma' ≤ 1 / 2 - kappa → 0 < eps →
    ∀ᶠ x : ℝ in atTop, ∀ m n u : ℕ,
      m * n = 2 * u + 1 → x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
      gamma < Real.log n / L x → Real.log n / L x ≤ gamma' →
      proxyConstant (.rough gamma) x S m ≤
        (sSup ((fun a : ℝ => roughDensity gamma (1 - a)) '' Set.Icc gamma gamma') + eps) /
          (L x * sieveProduct (W x)))

structure ProxyInputs : Prop where
  discrepancy : ProxyDiscrepancy
  densities : ProxyDensities
  identities : DensityIdentities
  products : SieveProducts

/-- P8 boundary: no Type II input, so S is chosen after Type II's B. -/
abbrev proxy_inputs_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (_hs : SieveInputs),
    ProxyInputs
end Erdos821.Blueprint
