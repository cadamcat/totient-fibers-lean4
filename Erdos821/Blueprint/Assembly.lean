import Erdos821.Blueprint.Extraction
import Erdos821.Count.Count
import Erdos821.P1.ClassicalInputs

/-! All ten package interfaces meet here. Both assembly proofs have no placeholder. -/
namespace Erdos821.Blueprint

/-- Proof functions expose the dependency order without using placeholder proofs. -/
structure PackageInterfaces : Prop where
  classical : ClassicalInputs
  sieve : ClassicalInputs → SieveInputs
  transference : ClassicalInputs → TransferenceInputs
  ideal : ClassicalInputs → IdealInputs
  shift : ClassicalInputs → SieveInputs → TransferenceInputs → IdealInputs → ShiftEstimate
  typeII : ClassicalInputs → ShiftEstimate → TypeIIEstimate
  proxies : ClassicalInputs → SieveInputs → ProxyInputs
  candidateGeometry : ∀ δ : ℝ, 0 < δ → δ < 1 / 4 → ∃ C : CandidateData, C.Geometry δ
  candidateBounds : ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ
  candidateTypeI : ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ → C.TypeI
  balanced : ∀ (δ : ℝ) (C : CandidateData),
    C.Geometry δ → C.Bounds δ → BalancedRoughBound C
  extraction : ClassicalInputs → SieveInputs → TypeIIEstimate → ProxyInputs →
    ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ → C.TypeI →
      BalancedRoughBound C → PrimeExtraction C
  count : ∀ (δ : ℝ), 0 < δ → ∀ C : CandidateData, C.Bounds δ → PrimeExtraction C →
    ∀ σ : ℝ, 0 < σ → ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (1 - σ) ≤ ((Erdos821.smoothShiftedPrimes δ x).card : ℝ)

/-- The dependency assembly itself can be audited without sorry-backed interfaces. -/
theorem supply_of_package_interfaces (h : PackageInterfaces) : Erdos821.SmoothShiftedPrimeSupply := by
  have hc := h.classical
  have hs := h.sieve hc
  have ht := h.transference hc
  have hi := h.ideal hc
  have hshift := h.shift hc hs ht hi
  have hii := h.typeII hc hshift
  have hp := h.proxies hc hs
  intro δ hδ hδ'
  obtain ⟨C, hC⟩ := h.candidateGeometry δ hδ hδ'
  have hb := h.candidateBounds δ C hC
  have htypeI := h.candidateTypeI δ C hC hb
  have hbal := h.balanced δ C hC hb
  have hextract := h.extraction hc hs hii hp δ C hC hb htypeI hbal
  exact h.count δ hδ C hb hextract

end Erdos821.Blueprint
namespace Erdos821
open Blueprint

end Erdos821
