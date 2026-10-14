import Erdos821.P10.Extraction

/-! Exact remaining contracts for the P10 extraction assembly. -/
noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.P10
attribute [local instance] Classical.propDecidable

/-- Actual rough-cofactor mass, summed over the fixed exponent mesh. -/
def unbalancedMeshMass (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (b κ : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,
    ∑ z ∈ ((Finset.Icc 1 ⌊2 * x⌋₊ ×ˢ
        primeExponentBin (densityMeshPoint b κ N i)
          (densityMeshPoint b κ N (i + 1)) x).filter
            (fun z => z.2 ∣ 2 * z.1 + 1)),
      C.weighted x jstar z.1 *
        test (.rough (densityMeshPoint b κ N i)) x ((2 * z.1 + 1) / z.2)

/-- The composites whose least prime factor is above the unbalanced range. -/
def balancedCompositeMass (C : CandidateData) (x : ℝ) (jstar : ℕ) (κ : ℝ) : ℝ :=
  ∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter
    (fun u => ¬ Nat.Prime (2 * u + 1) ∧
      x ^ (1 / 2 - κ) < (Nat.minFac (2 * u + 1) : ℝ)),
    C.weighted x jstar u

/-- Choose the small presieve exponent before the exceptional slot. -/
def SharpPresieveTask : Prop :=
  ∀ (hc : ClassicalInputs) (hs : SieveInputs) (hp : ProxyInputs)
    (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ → C.TypeI →
    ∀ bmax ε : ℝ, 0 < bmax → 0 < ε →
      ∃ b : ℝ, 0 < b ∧ b < bmax ∧
        ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
          (singularSeries * roughDensity b 1 - ε) * C.mass x jstar / Analytic.L x ≤
            candidateSiftedMass C x jstar (x ^ b)

def UnbalancedMeshTask : Prop :=
  ∀ (hc : ClassicalInputs) (hs : SieveInputs) (hII : TypeIIEstimate)
    (hp : ProxyInputs) (δ : ℝ) (C : CandidateData),
    C.Geometry δ → C.Bounds δ → C.TypeI →
    ∀ b κ ε : ℝ, 0 < b → b < κ → 0 < κ → κ < 1 / 50 → 0 < ε →
      ∀ jstar : ℕ, C.j₀ ≤ jstar →
        C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < b / 12 →
        ∃ N : ℕ, 0 < N ∧ ∀ᶠ x : ℝ in atTop,
          unbalancedMeshMass C x jstar b κ N ≤
            singularSeries * (roughDensity b 1 - 1 + ε) *
              C.mass x jstar / Analytic.L x

/-- Cover sifted composites by their least-factor mesh bin or the balanced part. -/
def CompositeCoverageTask : Prop :=
  ∀ (δ : ℝ) (C : CandidateData), C.Bounds δ →
    ∀ b κ : ℝ, 0 < b → b < κ → 0 < κ → κ < 1 / 50 →
      ∀ N : ℕ, 0 < N → ∀ jstar : ℕ, C.j₀ ≤ jstar →
        ∀ᶠ x : ℝ in atTop,
          candidateSiftedMass C x jstar (x ^ b) ≤
            C.primeMass x jstar + unbalancedMeshMass C x jstar b κ N +
              balancedCompositeMass C x jstar κ

/-- The comparison constant precedes κ, the rough slot and proxy precision. -/
def BalancedCompositeTask : Prop :=
  ∀ (hc : ClassicalInputs) (hII : TypeIIEstimate) (hp : ProxyInputs)
    (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ →
    BalancedRoughBound C →
      ∃ K : ℝ, 0 < K ∧ ∀ κ bstar : ℝ,
        0 < κ → κ < 1 / 50 → 0 < bstar → bstar < 1 / 10 →
          ∀ jstar : ℕ, C.j₀ ≤ jstar →
            C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < bstar / 4 →
              ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
                balancedCompositeMass C x jstar κ ≤
                  (K * κ + ε) * C.mass x jstar / Analytic.L x

end Erdos821.P7Core
