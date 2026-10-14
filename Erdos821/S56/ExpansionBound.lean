import Erdos821.S56.PreCauchyTask

noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- After pre-Cauchy reconstruction, integration pays only the fixed cutoff
mass and the already bounded total variation of the branch coefficients. -/
theorem pre_cauchy_expansion_bound (D : BandData) (x : ℝ) (jstar : ℕ)
    (Cs K0 U V M : ℝ) (a : Bool → ℝ → ℂ) (f : ℝ → ℂ) (alpha beta : ℕ → ℂ)
    (ha : ∀ b, Integrable (a b)) (hf : Integrable f) (hM : 0 ≤ M)
    (hsep : ∀ (delta : ProcessedIndex D x jstar → Bool) (xi : ProcessedIndex D x jstar → ℝ)
      (t : ℝ), ‖t‖ ≤ L x → ‖branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t‖ ≤ M) :
    ‖preCauchyExpansion D x jstar Cs K0 U V a f alpha beta‖ ≤
      M*(∫ t, ‖f t‖)*∑ delta : ProcessedIndex D x jstar → Bool,
        ∫ xi : ProcessedIndex D x jstar → ℝ,
          ‖branchFourierCoefficient (pureIndices D x jstar).card a delta xi‖ := by
  let Mf := ∫ t, ‖f t‖
  have hMf : 0 ≤ Mf := integral_nonneg (fun _ => norm_nonneg _)
  have hs : MeasurableSet {t : ℝ | ‖t‖ ≤ L x} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have hinner (delta : ProcessedIndex D x jstar → Bool) (xi : ProcessedIndex D x jstar → ℝ) :
      ‖∫ t in {t : ℝ | ‖t‖ ≤ L x}, f t*branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t‖ ≤
        M*Mf := by
    calc
      _ ≤ ∫ t in {t : ℝ | ‖t‖ ≤ L x}, M*‖f t‖ :=
        norm_integral_le_of_norm_le (hf.norm.const_mul M).integrableOn (by
          filter_upwards [ae_restrict_mem hs] with t ht
          rw [norm_mul]
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hsep delta xi t ht) (norm_nonneg _))
      _ = M*∫ t in {t : ℝ | ‖t‖ ≤ L x}, ‖f t‖ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hf.norm (Eventually.of_forall (fun _ => norm_nonneg _))) hM
  have houter (delta : ProcessedIndex D x jstar → Bool) :
      ‖∫ xi in {xi : ProcessedIndex D x jstar → ℝ | ∀ i, ‖xi i‖ ≤ L x},
        branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
          ∫ t in {t : ℝ | ‖t‖ ≤ L x}, f t*branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t‖ ≤
        (M*Mf)*∫ xi : ProcessedIndex D x jstar → ℝ,
          ‖branchFourierCoefficient (pureIndices D x jstar).card a delta xi‖ := by
    have hab := branch_coefficient_integrable (pureIndices D x jstar).card a ha delta
    calc
      _ ≤ ∫ xi in {xi : ProcessedIndex D x jstar → ℝ | ∀ i, ‖xi i‖ ≤ L x},
          (M*Mf)*‖branchFourierCoefficient (pureIndices D x jstar).card a delta xi‖ :=
        norm_integral_le_of_norm_le (hab.norm.const_mul (M*Mf)).integrableOn (by
          filter_upwards with xi
          rw [norm_mul]
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hinner delta xi) (norm_nonneg _))
      _ = (M*Mf)*∫ xi in {xi : ProcessedIndex D x jstar → ℝ | ∀ i, ‖xi i‖ ≤ L x},
          ‖branchFourierCoefficient (pureIndices D x jstar).card a delta xi‖ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hab.norm (Eventually.of_forall (fun _ => norm_nonneg _))) (mul_nonneg hM hMf)
  calc
    _ ≤ ∑ delta : ProcessedIndex D x jstar → Bool,
        ‖∫ xi in {xi : ProcessedIndex D x jstar → ℝ | ∀ i, ‖xi i‖ ≤ L x},
          branchFourierCoefficient (pureIndices D x jstar).card a delta xi *
            ∫ t in {t : ℝ | ‖t‖ ≤ L x}, f t*branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ delta : ProcessedIndex D x jstar → Bool, (M*Mf)*
        ∫ xi : ProcessedIndex D x jstar → ℝ,
          ‖branchFourierCoefficient (pureIndices D x jstar).card a delta xi‖ :=
      Finset.sum_le_sum (fun delta _ => houter delta)
    _ = _ := by rw [Finset.mul_sum]


end Erdos821.S56Core
