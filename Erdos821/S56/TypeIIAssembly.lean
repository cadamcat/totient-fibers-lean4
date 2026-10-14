import Erdos821.S56.SeparatedBranchBound
import Erdos821.S56.ExpansionBound
import Erdos821.S56.ProcessedCoefficientBound

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem typeII_of_tasks (hc : ClassicalInputs) (hshift : ShiftEstimate)
    (hSplit : SlotCoefficientSplitTask) (hProcessed : ProcessedCoefficientBoundTask)
    (hApprox : PreCauchyApproximationTask) : TypeIIEstimate := by
  intro D hD Dsave b C hDsave hb hC jstar heta psi hpsi hsupp
  obtain ⟨a, ha, hm, hrep⟩ := transition_fourier_coefficients (argumentRadius D)
  obtain ⟨f, hf, hfm, hfRep⟩ := fixed_fourier (logCutoff psi)
    (log_cutoff_smooth psi hpsi) (log_cutoff_compact psi hsupp)
  obtain ⟨Cs, hCs, hApprox⟩ := hApprox hSplit hc D hD psi hpsi hsupp a f ha hm hrep hf hfm hfRep
  obtain ⟨Cf, hCf, hmass⟩ := branch_mass_polylog D hD a
  obtain ⟨K0, B, K, hK0, hB, hK, hsep⟩ := separated_branch_estimate hc hshift hProcessed D hD
    (Dsave+Cf) b C Cs (by positivity) hb hC hCs jstar heta
  obtain ⟨Ke, hKe, herr⟩ := hApprox b C hb hC jstar heta Dsave K0 hDsave hK0
  let Mf := ∫ t, ‖f t‖
  have hMf : 0 ≤ Mf := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨B, Ke+K*Mf+1, hB, by positivity, ?_⟩
  filter_upwards [herr, hsep, hmass, eventually_ge_atTop 1,
    tendsto_L.eventually (eventually_ge_atTop 1)] with x herr hsep hmass hx hL
  intro U V alpha beta hUVlo hUVhi hUlo hUhi hVlo hVhi hcoeff hrough hdisc
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hLp : 0 < L x := zero_lt_one.trans_le hL
  have hbranch := hsep U V alpha beta hUVlo hUVhi hUlo hUhi hVlo hVhi hcoeff hrough hdisc
  have hraw := pre_cauchy_expansion_bound D x jstar Cs K0 U V (K*x*L x^(-(Dsave+Cf)))
    a f alpha beta ha hf (by positivity) hbranch
  have hexpansion : ‖preCauchyExpansion D x jstar Cs K0 U V a f alpha beta‖ ≤
      K*Mf*x*L x^(-Dsave) := by
    calc
      _ ≤ _ := hraw
      _ ≤ (K*x*L x^(-(Dsave+Cf)))*Mf*L x^Cf :=
        mul_le_mul_of_nonneg_left (hmass jstar) (by positivity)
      _ = _ := by
        rw [show -Dsave = -(Dsave+Cf)+Cf by ring, Real.rpow_add hLp]
        ring
  calc
    ‖typeIISum D x jstar U V psi alpha beta‖ =
        ‖(typeIISum D x jstar U V psi alpha beta-preCauchyExpansion D x jstar Cs K0 U V a f alpha beta)+
          preCauchyExpansion D x jstar Cs K0 U V a f alpha beta‖ := by congr 1; ring
    _ ≤ ‖typeIISum D x jstar U V psi alpha beta-preCauchyExpansion D x jstar Cs K0 U V a f alpha beta‖+
        ‖preCauchyExpansion D x jstar Cs K0 U V a f alpha beta‖ := norm_add_le _ _
    _ ≤ Ke*x*L x^(-Dsave)+K*Mf*x*L x^(-Dsave) := add_le_add
      (herr U V alpha beta hUVlo hUVhi hUlo hUhi hVlo hVhi hcoeff hrough) hexpansion
    _ ≤ (Ke+K*Mf+1)*x*L x^(-Dsave) := by
      have hp : 0 ≤ x*L x^(-Dsave) := by positivity
      nlinarith


/-- The partial-slot coefficient task is discharged by its accepted proof.
Only finite splitting and pre-Cauchy reconstruction remain as hypotheses. -/
theorem typeII_of_two_tasks (hc : ClassicalInputs) (hshift : ShiftEstimate)
    (hSplit : SlotCoefficientSplitTask) (hApprox : PreCauchyApproximationTask) : TypeIIEstimate :=
  typeII_of_tasks hc hshift hSplit processed_coefficient_bound hApprox


end Erdos821.S56Core
