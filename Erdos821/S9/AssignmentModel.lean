import Erdos821.S9.EulerTasks

noncomputable section
open scoped BigOperators
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core

def assignmentCoefficient (C : CandidateData) (x : ℝ) : ℝ :=
  listNormalizer C.bands x * (Fintype.card (MacroSlotIndex C)).factorial *
    ∏ g, (mass (C.bands.groups x) g)⁻¹

def assignmentModulus (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (m : MicroAssignments C x jstar) (marks : GlobalMarkChoices (C.bands.groups x)) : ℕ :=
  microAssignmentProduct C x jstar m * globalMarkProduct (C.bands.groups x) marks

def assignmentMaskPrimes (C : CandidateData) (x : ℝ)
    (marks : GlobalMarkChoices (C.bands.groups x)) : Finset ℕ :=
  groupPrimeSet (C.bands.groups x) \ globalMarkImage (C.bands.groups x) marks

def microHarmonicMass (C : CandidateData) (x : ℝ) (jstar : ℕ) : ℝ :=
  listNormalizer C.bands x * (Fintype.card (MacroSlotIndex C)).factorial *
    ∏ s : MicroSlotSubtype C x,
      ∑ v : C.bands.SlotValue x jstar s.val, (v.val : ℝ)⁻¹

end Erdos821.S56Core
