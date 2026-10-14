import Erdos821.S56.PreCauchyTask
import Erdos821.S56.SeparatedSaving
import Erdos821.S56.PureMultiplicity
import Erdos821.S56.BandEndpoint

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The post-Cauchy theorem applies to every reconstructed Fourier branch.
Partial slot counts bound all frequencies, so the xi variables need no
restriction here. Only the fixed cutoff's frequency t is truncated. -/
theorem separated_branch_estimate (hc : ClassicalInputs) (hshift : ShiftEstimate)
    (hProcessed : ProcessedCoefficientBoundTask) (D : BandData) (hD : D.Valid)
    (A b C0 Cs : ℝ) (hA : 0 < A) (hb : 0 < b) (hC0 : 0 < C0) (hCs : 0 < Cs)
    (jstar : ℕ) (heta : D.c₂*D.s'/D.ratio^jstar < b/4) :
    ∃ K0 B K : ℝ, 0 < K0 ∧ 0 < B ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ U V : ℝ, ∀ alpha beta : ℕ → ℂ,
        x/8 ≤ U*V → U*V ≤ 8*x →
        x^b ≤ U → U ≤ x^(1-b) → x^b ≤ V → V ≤ x^(1-b) →
        (∀ n, ‖alpha n‖ ≤ L x^C0 ∧ ‖beta n‖ ≤ L x^C0) →
        (∀ n, alpha n ≠ 0 → rough (W x) n) →
        discrepancy x B (restricted U alpha) →
        ∀ (delta : ProcessedIndex D x jstar → Bool) (xi : ProcessedIndex D x jstar → ℝ) (t : ℝ),
          ‖t‖ ≤ L x → ‖branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t‖ ≤ K*x*L x^(-A) := by
  obtain ⟨Cp, hCp, hp⟩ := hProcessed pure_slot_multiplicity D hD
  let C := max (max C0 Cp) 2+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0C : C0 ≤ C := by
    have h := (le_max_left C0 Cp).trans (le_max_left (max C0 Cp) 2)
    change C0 ≤ max (max C0 Cp) 2+1
    linarith
  have hCpC : Cp ≤ C := by
    have h := (le_max_right C0 Cp).trans (le_max_left (max C0 Cp) 2)
    change Cp ≤ max (max C0 Cp) 2+1
    linarith
  have h2C : (2:ℝ) ≤ C := by
    change (2:ℝ) ≤ max (max C0 Cp) 2+1
    linarith [le_max_right (max C0 Cp) 2]
  obtain ⟨htau, htaueta, hetaquarter⟩ := exceptional_exponents D hD jstar
  obtain ⟨K0, B, K, hK0, hB, hK, hsep⟩ := separated_estimate hc hshift D.geometry A b C Cs
    (D.c₁*D.s'/D.ratio^jstar) (D.c₂*D.s'/D.ratio^jstar)
    hA hb hC hCs htau htaueta hetaquarter heta
  have hdata := hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, hcmin, hcmax, hvalid⟩ := hdata
  refine ⟨K0, B, K, hK0, hB, hK, ?_⟩
  filter_upwards [hp, hsep, hvalid, eventually_ge_atTop 1,
    tendsto_L.eventually (eventually_ge_atTop (max 1 (2*Real.pi)))] with x hp hsep hvalid hx hL
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hL1 : 1 ≤ L x := (le_max_left _ _).trans hL
  have hLpi : 2*Real.pi ≤ L x := (le_max_right _ _).trans hL
  have hLp : 0 < L x := zero_lt_one.trans_le hL1
  intro U V alpha beta hUVlo hUVhi hUlo hUhi hVlo hVhi hcoeff hrough hdisc delta xi t ht
  let nu := branchFrequency D x jstar delta xi
  have hpC : L x^Cp ≤ L x^C := Real.rpow_le_rpow_of_exponent_le hL1 hCpC
  have hC0pow : L x^C0 ≤ L x^C := Real.rpow_le_rpow_of_exponent_le hL1 hC0C
  have hrho : |2*Real.pi*t| ≤ L x^C := by
    have hraw := mul_le_mul hLpi (by simpa only [Real.norm_eq_abs] using ht)
      (abs_nonneg t) (by positivity : (0:ℝ) ≤ L x)
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    calc
      _ ≤ L x*L x := hraw
      _ = L x^(2:ℝ) := by rw [Real.rpow_two]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 h2C
  have hae : ∀ v : ℕ,
      ‖((((D.r₀.factorial:ℝ)^(D.last x+1))⁻¹:ℝ):ℂ)*
        Erdos821.Blueprint.Analytic.mellin v (2*Real.pi*t)*processedCoefficient D x jstar delta true nu v‖ ≤ L x^C := by
    intro v
    obtain ⟨hn0, hn1⟩ := factorial_normalization_le_one D x
    rw [norm_mul, norm_mul, norm_mellin, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn0]
    calc
      _ ≤ ‖processedCoefficient D x jstar delta true nu v‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hn1
          (norm_nonneg (processedCoefficient D x jstar delta true nu v))
      _ ≤ _ := (hp jstar delta true nu v).trans hpC
  have hh := hsep (D.groups x) U V
    (Real.exp (D.c₁*D.scale x jstar)) (Real.exp (D.c₂*D.scale x jstar)) (2*Real.pi*t) 0
    (fun v => ((((D.r₀.factorial:ℝ)^(D.last x+1))⁻¹:ℝ):ℂ)*
      Erdos821.Blueprint.Analytic.mellin v (2*Real.pi*t)*processedCoefficient D x jstar delta true nu v)
    (processedCoefficient D x jstar delta false nu) alpha beta
    hvalid.1 hUVlo hUVhi hUlo hUhi hVlo hVhi
    (by rw [band_endpoint_power D x D.c₁ jstar hxpos])
    (by rw [band_endpoint_power D x D.c₁ jstar hxpos, band_endpoint_power D x D.c₂ jstar hxpos]
        exact Real.rpow_le_rpow_of_exponent_le hx htaueta.le)
    (by rw [band_endpoint_power D x D.c₂ jstar hxpos]) hrho
    (by simp; positivity)
    (fun n => ⟨hae n, (hp jstar delta false nu n).trans hpC,
      (hcoeff n).1.trans hC0pow, (hcoeff n).2.trans hC0pow⟩) hrough hdisc
  simpa only [branchSeparatedValue, norm_mul, norm_e, one_mul] using hh


end Erdos821.S56Core
