import Erdos821.S56.FourierCost
import Erdos821.S56.ProductError
import Erdos821.S56.FrequencyBound

noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def truncatedTransition (a : Bool → ℝ → ℂ) (b : Bool) (R t : ℝ) : ℂ :=
  ∫ xi in {xi : ℝ | ‖xi‖ ≤ R}, a b xi * e (xi*t)

def truncatedBranch (n : ℕ) (a : Bool → ℝ → ℂ) (R target : ℝ)
    (v s : Fin n → ℝ) (delta : Fin n → Bool) : ℂ :=
  ∏ i, truncatedTransition a (delta i) R
    ((Erdos821.S56.residual target v delta i.val-v i)/s i)

theorem truncated_branch_error (n k : ℕ) (radius R target M Mk : ℝ)
    (v s : Fin n → ℝ) (a : Bool → ℝ → ℂ)
    (ha : ∀ b, Integrable (a b))
    (hrep : ∀ b t, (transition radius b t : ℂ) = ∫ xi, a b xi*e (xi*t))
    (hm : ∀ b, Integrable (fun xi => ‖xi‖^k*‖a b xi‖))
    (hM : 1 ≤ M) (hMk : 0 ≤ Mk) (hR : 0 < R)
    (hmass : ∀ b, (∫ xi, ‖a b xi‖) ≤ M)
    (hmoment : ∀ b, (∫ xi, ‖xi‖^k*‖a b xi‖) ≤ Mk) :
    (∑ delta : Fin n → Bool,
      ‖(clippedBranchMass n target v s radius delta : ℂ)-truncatedBranch n a R target v s delta‖) ≤
      (n:ℝ)*(R^k)⁻¹*Mk*(2*M)^n := by
  have herror (delta : Fin n → Bool) :
      ‖(clippedBranchMass n target v s radius delta : ℂ)-truncatedBranch n a R target v s delta‖ ≤
        (n:ℝ)*((R^k)⁻¹*Mk)*M^n := by
    simp only [clippedBranchMass, Complex.ofReal_prod, truncatedBranch]
    apply (product_error_bound Finset.univ _ _ M ((R^k)⁻¹*Mk) hM (by positivity) ?_ ?_ ?_).trans_eq
      (by simp)
    · intro i _
      obtain ⟨h0, h1⟩ := transition_bounds radius
        ((Erdos821.S56.residual target v delta i.val-v i)/s i) (delta i)
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using h1.trans hM
    · intro i _
      exact (fourier_truncated_norm_le_mass (a (delta i)) (ha _) R _).trans (hmass _)
    · intro i _
      exact (fixed_fourier_truncation (fun t => (transition radius (delta i) t : ℂ))
        (a (delta i)) (ha _) (hrep _) k (hm _) R hR _).trans
          (mul_le_mul_of_nonneg_left (hmoment _) (by positivity))
  calc
    _ ≤ ∑ _delta : Fin n → Bool, (n:ℝ)*((R^k)⁻¹*Mk)*M^n :=
      Finset.sum_le_sum (fun delta _ => herror delta)
    _ = _ := by simp [Fintype.card_fun, mul_pow]; ring

/-- The tensor cutoff error is smaller than every fixed log power, summed
over all allocation patterns before Cauchy and uniformly in all arguments. -/
theorem branch_truncation_polylog (D : BandData) (hD : D.Valid) (radius : ℝ)
    (a : Bool → ℝ → ℂ) (ha : ∀ b, Integrable (a b))
    (hrep : ∀ b t, (transition radius b t : ℂ) = ∫ xi, a b xi*e (xi*t))
    (hm : ∀ b k, Integrable (fun xi => ‖xi‖^k*‖a b xi‖))
    (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ,
      ∀ target : ℝ, ∀ v s : ProcessedIndex D x jstar → ℝ,
        (∑ delta : ProcessedIndex D x jstar → Bool,
          ‖(clippedBranchMass (pureIndices D x jstar).card target v s radius delta : ℂ)-
            truncatedBranch (pureIndices D x jstar).card a (L x) target v s delta‖) ≤ K*L x^(-A) := by
  let M := max 1 (max (∫ xi, ‖a false xi‖) (∫ xi, ‖a true xi‖))
  have hM : 1 ≤ M := le_max_left _ _
  have hmass : ∀ b, (∫ xi, ‖a b xi‖) ≤ M := by
    intro b
    cases b
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Cc, hCc, hc⟩ := processed_card_bound D hD
  let Q := Cc*Real.log (2*M)
  obtain ⟨k, hk⟩ := exists_nat_gt (A+Q+1)
  let Mk := max (∫ xi, ‖xi‖^k*‖a false xi‖) (∫ xi, ‖xi‖^k*‖a true xi‖)+1
  have hMk : 0 < Mk := by
    have hh : 0 ≤ ∫ xi, ‖xi‖^k*‖a false xi‖ := integral_nonneg (fun _ => by positivity)
    exact add_pos_of_nonneg_of_pos (hh.trans (le_max_left _ _)) zero_lt_one
  have hmoment : ∀ b, (∫ xi, ‖xi‖^k*‖a b xi‖) ≤ Mk := by
    intro b
    cases b
    · exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
    · exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨Mk, hMk, ?_⟩
  filter_upwards [hc, eventually_processed_count_le_L D hD,
    tendsto_L.eventually (eventually_ge_atTop 1)] with x hc hn hL
  intro jstar target v s
  have hLp : 0 < L x := zero_lt_one.trans_le hL
  have hMp : 0 ≤ M := zero_le_one.trans hM
  have hpow := polylog_of_loglog_count x Cc (2*M) (pureIndices D x jstar).card
    hLp (by linarith) (hc jstar)
  have hp0 : 0 ≤ (L x^k)⁻¹*Mk := by positivity
  have hfirst := mul_le_mul_of_nonneg_right (hn jstar) hp0
  have hboth := mul_le_mul hfirst hpow (pow_nonneg (by linarith : 0 ≤ 2*M) _) (by positivity)
  have hid : L x*((L x^k)⁻¹*Mk)*L x^Q = Mk*L x^(1-(k:ℝ)+Q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hLp.le]
    rw [show 1-(k:ℝ)+Q = -(k:ℝ)+1+Q by ring,
      Real.rpow_add hLp, Real.rpow_add hLp, Real.rpow_one]
    ring
  have hfinal := Real.rpow_le_rpow_of_exponent_le hL (by linarith : 1-(k:ℝ)+Q ≤ -A)
  calc
    _ ≤ (pureIndices D x jstar).card*(L x^k)⁻¹*Mk*(2*M)^(pureIndices D x jstar).card :=
      truncated_branch_error _ k radius (L x) target M Mk v s a ha hrep
        (fun b => hm b k) hM hMk.le hLp hmass hmoment
    _ ≤ L x*((L x^k)⁻¹*Mk)*L x^Q := by simpa only [mul_assoc, Q] using hboth
    _ = Mk*L x^(1-(k:ℝ)+Q) := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left hfinal hMk.le


end Erdos821.S56Core
