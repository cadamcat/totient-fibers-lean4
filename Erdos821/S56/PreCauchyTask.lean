import Erdos821.S56.SlotSplitTasks
import Erdos821.S56.CutoffFourier
import Erdos821.S56.BranchTruncation
import Erdos821.S56.BilinearError
import Erdos821.S56.TailSaving

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def branchFrequency (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : ProcessedIndex D x jstar → Bool) (xi : ProcessedIndex D x jstar → ℝ)
    (i : ProcessedIndex D x jstar) : ℝ :=
  2*Real.pi*Erdos821.S56.slotFrequency (processedScale D x jstar) xi delta i

def branchSeparatedValue (D : BandData) (x : ℝ) (jstar : ℕ) (Cs K0 U V : ℝ)
    (alpha beta : ℕ → ℂ) (delta : ProcessedIndex D x jstar → Bool)
    (xi : ProcessedIndex D x jstar → ℝ) (t : ℝ) : ℂ :=
  let E := U*L x^(-K0)
  let nu := branchFrequency D x jstar delta xi
  e (Real.log E*∑ i, xi i/processedScale D x jstar i)*e (-t*Real.log x)*
    separatedSum (E*L x^(-Cs)) E U V
      (fun v => ((((D.r₀.factorial:ℝ)^(D.last x+1))⁻¹:ℝ):ℂ)*
        Erdos821.Blueprint.Analytic.mellin v (2*Real.pi*t)*
          processedCoefficient D x jstar delta true nu v)
      (hCoefficient D.geometry (D.groups x) x
        (Real.exp (D.c₁*D.scale x jstar)) (Real.exp (D.c₂*D.scale x jstar))
        (2*Real.pi*t) 0 (processedCoefficient D x jstar delta false nu)) alpha beta

def preCauchyExpansion (D : BandData) (x : ℝ) (jstar : ℕ) (Cs K0 U V : ℝ)
    (a : Bool → ℝ → ℂ) (f : ℝ → ℂ) (alpha beta : ℕ → ℂ) : ℂ :=
  ∑ delta : ProcessedIndex D x jstar → Bool,
    ∫ xi in {xi : ProcessedIndex D x jstar → ℝ | ∀ i, ‖xi i‖ ≤ L x},
      branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
        ∫ t in {t : ℝ | ‖t‖ ≤ L x}, f t*branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t

/-- Exact finite slot splitting and fixed Fourier inversion reconstruct the
original bilinear sum with arbitrarily small aggregate error. This task is
independent of ShiftEstimate, discrepancy and the post-Cauchy estimate.
Cs is chosen before b, jstar, A and K0. All original factorials are retained. -/
def PreCauchyApproximationTask : Prop :=
  SlotCoefficientSplitTask → ClassicalInputs →
  ∀ D : BandData, D.Valid → ∀ psi : ℝ → ℝ,
    ContDiff ℝ ∞ psi → Function.support psi ⊆ Set.Icc 1 2 →
    ∀ (a : Bool → ℝ → ℂ) (f : ℝ → ℂ),
      (∀ b, Integrable (a b)) →
      (∀ b k, Integrable (fun xi => ‖xi‖^k*‖a b xi‖)) →
      (∀ b z, (transition (argumentRadius D) b z : ℂ) = ∫ xi, a b xi*e (xi*z)) →
      Integrable f → (∀ k, Integrable (fun t => ‖t‖^k*‖f t‖)) →
      (∀ z, (psi (Real.exp z) : ℂ) = ∫ t, f t*e (t*z)) →
      ∃ Cs : ℝ, 0 < Cs ∧ ∀ b C0 : ℝ, 0 < b → 0 < C0 → ∀ jstar : ℕ,
        D.c₂*D.s'/D.ratio^jstar < b/4 → ∀ A K0 : ℝ, 0 < A → 0 < K0 →
          ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ U V : ℝ, ∀ alpha beta : ℕ → ℂ,
            x/8 ≤ U*V → U*V ≤ 8*x →
            x^b ≤ U → U ≤ x^(1-b) → x^b ≤ V → V ≤ x^(1-b) →
            (∀ n, ‖alpha n‖ ≤ L x^C0 ∧ ‖beta n‖ ≤ L x^C0) →
            (∀ n, alpha n ≠ 0 → rough (W x) n) →
            ‖typeIISum D x jstar U V psi alpha beta -
              preCauchyExpansion D x jstar Cs K0 U V a f alpha beta‖ ≤ K*x*L x^(-A)

end Erdos821.S56Core
