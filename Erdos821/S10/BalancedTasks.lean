import Erdos821.S10.Tasks

/-! Independent balanced-composite obligations: arithmetic, dyads, replacements. -/
noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.P10
attribute [local instance] Classical.propDecidable

def balancedWindow (x κ : ℝ) : Finset ℕ :=
  Finset.Icc ⌈x ^ (1 / 2 - 2 * κ)⌉₊ ⌊x ^ (1 / 2 + 2 * κ)⌋₊

def balancedPairWindowMass (C : CandidateData) (x : ℝ) (jstar : ℕ) (κ : ℝ)
    (a b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ balancedWindow x κ, ∑ n ∈ balancedWindow x κ,
    if Odd (m * n) ∧ 1 < m * n then
      C.weighted x jstar ((m * n - 1) / 2) * a m * b n else 0

def balancedPrimeWindowMass (C : CandidateData) (x : ℝ) (jstar : ℕ) (κ : ℝ) : ℝ :=
  balancedPairWindowMass C x jstar κ (test .prime x) (test .prime x)

def balancedRoughWindowMass (C : CandidateData) (x : ℝ) (jstar : ℕ) (κ : ℝ) : ℝ :=
  balancedPairWindowMass C x jstar κ
    (fun m => if Analytic.rough (Analytic.W x) m then 1 else 0)
    (fun n => if Analytic.rough (Analytic.W x) n then 1 else 0)

/-- Three large prime factors cannot divide a supported balanced composite. -/
def BalancedFactorCoverageTask : Prop :=
  ∀ (δ : ℝ) (C : CandidateData), C.Bounds δ →
    ∀ κ : ℝ, 0 < κ → κ < 1 / 50 →
      ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
        balancedCompositeMass C x jstar κ ≤ balancedPrimeWindowMass C x jstar κ

/-- Only O(κ log x + 1) supported dyadic pairs meet the balanced window. -/
def BalancedWindowRoughTask : Prop :=
  ∀ (hc : ClassicalInputs) (δ : ℝ) (C : CandidateData),
    C.Geometry δ → C.Bounds δ → BalancedRoughBound C →
      ∃ K : ℝ, 0 < K ∧ ∀ κ : ℝ, 0 < κ → κ < 1 / 50 →
        ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
          balancedRoughWindowMass C x jstar κ ≤
            K * (κ * Analytic.L x + 1) * C.mass x jstar *
              sieveProduct (Analytic.W x) ^ 2

/-- Replace the two prime indicators, with one uniform proxy-density constant. -/
def BalancedWindowPrimeTask : Prop :=
  ∀ (hc : ClassicalInputs) (hII : TypeIIEstimate) (hp : ProxyInputs)
    (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ →
      ∃ K : ℝ, 0 < K ∧ ∀ κ bstar : ℝ,
        0 < κ → κ < 1 / 50 → 0 < bstar → bstar < 1 / 10 →
          ∀ jstar : ℕ, C.j₀ ≤ jstar →
            C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4 →
              ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
                balancedPrimeWindowMass C x jstar κ ≤
                  K / (Analytic.L x ^ 2 * sieveProduct (Analytic.W x) ^ 2) *
                    balancedRoughWindowMass C x jstar κ +
                      ε * C.mass x jstar / Analytic.L x

end Erdos821.P7Core
