import Erdos821.S56.BlueprintInvariant

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def dyad (U : ℝ) : Finset ℕ := Finset.Ico ⌈U⌉₊ ⌈2 * U⌉₊

def roughCore (x lo hi sigma : ℝ) (c : ℕ → ℂ) (t : ℕ) : ℂ :=
  ∑ pr ∈ t.divisorsAntidiagonal,
    if lo ≤ (pr.1 : ℝ) ∧ (pr.1 : ℝ) ≤ hi ∧ rough (W x) pr.1 then
      mellin pr.1 sigma * c pr.2 else 0

def hCoefficient (P : Geometry) (G : PrimeGroups) (x lo hi rho sigma : ℝ)
    (c : ℕ → ℂ) (h : ℕ) : ℂ :=
  mellin h rho * markWeight G P.q (fun _ => P.ell) h *
    roughCore x lo hi sigma c (groupFreePart G h)

def separatedSum (emin E U V : ℝ) (ae ah alpha beta : ℕ → ℂ) : ℂ :=
  ∑ e ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊, ∑ n ∈ dyad V, ae e * beta n *
    ∑ m ∈ dyad U,
      if 0 < e ∧ 1 < m * n ∧ 2 * e ∣ m * n - 1 then
        alpha m * ah ((m * n - 1) / (2 * e)) else 0

def offDiagonalSum (E U V : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) : ℂ :=
  ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
    (etae (e / E) * etan (n / V) : ℝ) *
      ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e)))
        else 0

/-- The post-Cauchy half of §5. K₀ is fixed data here. Exact signed determinant
reconstruction, character congruence, and Fourier separation in log m, log m',
log z turn this literal off-diagonal sum into ShiftEstimate correlations.
All cutoff derivative constants and powers are fixed before B. -/
def OffDiagonalShiftTask : Prop :=
  ClassicalInputs → ShiftEstimate →
  ∀ (P : Geometry) (A b C Cs K0 tau eta : ℝ) (bounds : ℕ → ℝ),
    0 < A → 0 < b → 0 < C → 0 < Cs → 0 < K0 →
    0 < tau → tau < eta → eta < 1 / 4 → eta < b / 4 →
    (∀ j, 0 ≤ bounds j) →
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (U V lo hi rho sigma : ℝ)
        (c alpha : ℕ → ℂ) (etae etan : ℝ → ℝ),
        Admissible P x G → x / 8 ≤ U * V → U * V ≤ 8 * x →
        x ^ b ≤ U → U ≤ x ^ (1 - b) → x ^ b ≤ V → V ≤ x ^ (1 - b) →
        x ^ tau ≤ lo → lo ≤ hi → hi ≤ x ^ eta →
        |rho| ≤ L x ^ C → |sigma| ≤ L x ^ C →
        (∀ n, ‖alpha n‖ ≤ L x ^ C ∧ ‖c n‖ ≤ L x ^ C) →
        (∀ n, alpha n ≠ 0 → rough (W x) n) →
        discrepancy x B (restricted U alpha) →
        ContDiff ℝ ∞ etae → ContDiff ℝ ∞ etan →
        Function.support etae ⊆ Set.Icc (L x ^ (-Cs) / 2) 2 →
        Function.support etan ⊆ Set.Icc (1 / 2) 4 →
        (∀ j y, ‖iteratedDeriv j etae y‖ ≤ bounds j * L x ^ (C * (j + 1)) ∧
          ‖iteratedDeriv j etan y‖ ≤ bounds j * L x ^ (C * (j + 1))) →
        ‖offDiagonalSum (U * L x ^ (-K0)) U V etae etan
          (hCoefficient P G x lo hi rho sigma c) alpha‖ ≤ K * x * L x ^ (-A)

end Erdos821.S56Core
