import Erdos821.S56.FourierCost
import Erdos821.S56.CoreBound

noncomputable section
open Filter MeasureTheory
open scoped ContDiff

namespace Erdos821.S56Core
open Erdos821.Blueprint.Analytic

def logCutoff (psi : ℝ → ℝ) (t : ℝ) : ℂ := psi (Real.exp t)

theorem log_cutoff_smooth (psi : ℝ → ℝ) (hpsi : ContDiff ℝ ∞ psi) :
    ContDiff ℝ ∞ (logCutoff psi) :=
  Complex.ofRealCLM.contDiff.comp (hpsi.comp Real.contDiff_exp)

theorem log_cutoff_compact (psi : ℝ → ℝ)
    (hsupp : Function.support psi ⊆ Set.Icc 1 2) : HasCompactSupport (logCutoff psi) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  have hne : psi (Real.exp t) ≠ 0 := by
    simpa only [Function.mem_support, logCutoff, ne_eq, Complex.ofReal_eq_zero] using ht
  have hb := hsupp hne
  constructor
  · simpa using Real.log_le_log (by norm_num : (0:ℝ) < 1) hb.1
  · simpa using Real.log_le_log (Real.exp_pos t) hb.2

/-- The fixed smooth cutoff contributes one Fourier coefficient, independent
of x, K0 and the growing number of prime slots. -/
theorem cutoff_fourier (psi : ℝ → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (hsupp : Function.support psi ⊆ Set.Icc 1 2) :
    ∃ a : ℝ → ℂ, Integrable a ∧
      (∀ n : ℕ, Integrable (fun t => ‖t‖^n * ‖a t‖)) ∧
      ∀ u x : ℝ, 0 < u → 0 < x →
        (psi (u/x) : ℂ) = ∫ t, a t * e (-t*Real.log x) * mellin u (2*Real.pi*t) := by
  obtain ⟨a, ha, hm, hrep⟩ := fixed_fourier (logCutoff psi)
    (log_cutoff_smooth psi hpsi) (log_cutoff_compact psi hsupp)
  refine ⟨a, ha, hm, ?_⟩
  intro u x hu hx
  have hraw := hrep (Real.log (u/x))
  have hux : 0 < u/x := div_pos hu hx
  simp only [logCutoff, Real.exp_log hux] at hraw
  rw [hraw]
  apply integral_congr_ae
  filter_upwards with t
  rw [Real.log_div hu.ne' hx.ne']
  have heq : e (t*(Real.log u-Real.log x)) = e (-t*Real.log x)*mellin u (2*Real.pi*t) := by
    unfold e Erdos821.Blueprint.Analytic.mellin
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [heq]
  ring


end Erdos821.S56Core
