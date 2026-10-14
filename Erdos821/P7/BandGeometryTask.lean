import Erdos821.P7.EarlyParameters

noncomputable section
open Filter

namespace Erdos821.P7Core
open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

/-- The remaining analytic construction in `candidate_geometry`: prime groups
in the gaps between the dyadic Q-bands, and the last band at scale `20 log log x`.
This is a task statement, with no assumed proof.

Proof outline: set `s' = 1/(r₀*(1+6/5))`, and use `P7Core.lastBand s'`.
Enumerate the dyadic indices whose `[3s_j/2,9s_j/5]` interval is contained
in either `[L^(1/10),L^(1/5)]` or `[L^(3/10),L^(2/5)]`. The primes in
the exponential interval give each P-group. Dyadic inequalities give
pairwise disjointness and separation from every Q-band. Taking logarithms
of the dyadic endpoints gives both group counts comparable to `T`.
PNT/partial summation (or the stronger available Mertens asymptotic) gives
uniform reciprocal prime mass bounds near `log(6/5)` as their lower
endpoints tend to infinity. Import `Erdos821.P1.ClassicalInputs` for the
proved inputs. `LastBand.lean` supplies the terminal-scale and index
growth estimates, and `BandDisjoint.lean` supplies Q-band disjointness.
The already imported `Erdos970.Mertens.sum_prime_div_eq` and
`Erdos970.Mertens.E₂p.abs_le` give the stronger Mertens error directly;
the OAI `TotientAsymptotic.MertensReciprocal` wrapper is not prebuilt.
No candidate-mass estimate is part of this task. -/
def BandGeometryTask : Prop :=
  ∀ r₀ : ℕ, 6 ≤ r₀ → ∃ D : BandData,
    D.Valid ∧ D.r₀ = r₀ ∧ D.c₁ = 1 ∧ D.c₂ = 6 / 5 ∧ D.ratio = 2 ∧
    D.s' = 1 / ((r₀ : ℝ) * (1 + 6 / 5)) ∧
    D.geometry.q = 1 / 2 ∧ D.geometry.ell = 1 ∧
    D.geometry.a = 1 / 10 ∧ D.geometry.b = 1 / 5 ∧
    D.geometry.c = 3 / 10 ∧ D.geometry.d = 2 / 5 ∧
    (∀ᶠ x : ℝ in atTop,
      20 * T x ≤ D.c₁ * D.scale x (D.last x) ∧
      D.c₁ * D.scale x (D.last x + 1) < 20 * T x)

/-- Once the prime-band family has been constructed, all remaining choices
in the blueprint geometry follow from the fixed early parameters. -/
theorem candidate_geometry_of_bandGeometryTask (hbands : BandGeometryTask)
    (δ : ℝ) (hδ : 0 < δ) : ∃ C : CandidateData, C.Geometry δ := by
  obtain ⟨E⟩ := earlyParameters_nonempty δ hδ
  obtain ⟨D, hD, hr, hc₁, hc₂, hratio, hs, hq, hell, ha, hb, hc, hd, hlast⟩ :=
    hbands E.r₀ E.r₀_large
  have hDE : D.s' = E.s' := hs.trans E.s'_eq.symm
  let C : CandidateData := {
    bands := D, j₀ := E.j₀, prefixLen := E.prefixLen, micro := E.micro,
    theta := E.theta, psi := candidateBump }
  refine ⟨C, ?_⟩
  change D.Valid ∧ D.c₁ = 1 ∧ D.c₂ = 6 / 5 ∧ D.ratio = 2 ∧
    D.s' = 1 / ((D.r₀ : ℝ) * (D.c₁ + D.c₂)) ∧
    D.c₂ * D.s' < δ ∧ _
  dsimp only [C]
  refine ⟨hD, hc₁, hc₂, hratio, ?_, ?_, hlast, E.prefix_before, ?_,
    hq, hell, ha, hb, hc, hd, E.micro_before, ?_, ?_, E.theta_small, ?_,
    candidateBump_properties⟩
  · simpa only [hr, hc₁, hc₂] using hs
  · simpa only [hc₂, hDE] using E.smoothness_margin
  · simpa only [hr, hc₁, hc₂, hDE] using E.prefix_tail
  · simpa only [hc₂, hDE] using E.micro_lower
  · simpa only [hc₁, hDE, mul_one] using E.micro_upper
  · simpa only [hr, hc₂, hDE] using E.micro_tail

/-- Exact compatibility with the owned blueprint statement; only the explicit
prime-band construction remains as a hypothesis. -/
theorem candidateGeometryTask_closes (hbands : BandGeometryTask) :
    Erdos821.Blueprint.candidate_geometry_statement := by
  intro _ δ hδ _
  exact candidate_geometry_of_bandGeometryTask hbands δ hδ

example (hbands : BandGeometryTask) : Erdos821.Blueprint.candidate_geometry_statement :=
  candidateGeometryTask_closes hbands

end Erdos821.P7Core

