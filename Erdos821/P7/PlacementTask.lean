import Erdos821.Blueprint.Candidate

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def outsideSlotProduct (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (s : D.Slot x) : ℕ :=
  ∏ t ∈ Finset.univ.erase s, (z t).val

def prefixMidpointEvent (C : CandidateData) (epsilon : ℝ) {x : ℝ} {jstar : ℕ}
    (s : C.bands.Slot x) (z : C.bands.Lists x jstar) : Prop :=
  ∀ t : C.bands.Slot x, t ≠ s → t.1.val ≤ C.prefixLen →
    |Real.log (z t).val - (C.bands.c₁ + C.bands.c₂) / 2 * C.bands.scale x t.1.val| ≤
      epsilon * C.bands.scale x t.1.val

/-- The deterministic placement step in the lower candidate-mass comparison.
Its output fixes the prefix neighborhoods and P truncation before choosing
the positivity interval or the exceptional slot. No proof is assumed here.

Proof outline: remove one coordinate s in band zero and write the logarithm
of its complementary product as a sum over slots. The infinite midpoint sum
is L because `s'=1/(r₀*(c₁+c₂))` and the dyadic ratio is two. Within the
prefix, the displayed event gives total error at most
`2*r₀*epsilon*s'*L`. The full tail and omitted bands are bounded by the
geometry's strict prefix inequality, independently of the tail distribution
and of jstar. Choose, for example, epsilon sufficiently below
`(c₂-c₁)/(96*r₀)` and sigma below `(c₂-c₁)*s'/12`. Then log(r) contributes
at most sigma*L. The target window `[a*x,b*x]` differs from log(x) by the
fixed constants log(a),log(b), eventually smaller than the remaining free
slot margin. `jstar ≥ j₀ > prefixLen` keeps the exceptional coordinate out
of the prefix; its range still obeys the same deterministic tail bound.

The task contains no PNT, reciprocal sums, probability bounds, prime-group
construction, or mass assembly. Use the already proved slot bounds and
geometric-scale sums from `Erdos821/S56/` where their statements match. -/
def CandidatePlacementTask : Prop :=
  ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ →
    ∃ epsilon sigma : ℝ, 0 < epsilon ∧
      epsilon < (C.bands.c₂ - C.bands.c₁) / 4 ∧ 0 < sigma ∧
      ∀ a b : ℝ, 1 < a → a < b → b < 2 →
        ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
          ∀ s : C.bands.Slot x, s.1.val = 0 → s.2.val = 0 →
            ∀ z : C.bands.Lists x jstar, prefixMidpointEvent C epsilon s z →
              ∀ r : ℕ, 0 < r → (r : ℝ) ≤ x ^ sigma →
                Real.exp (C.bands.c₁ * C.bands.scale x 0) ≤
                    a * x / ((r : ℝ) * outsideSlotProduct C.bands z s) ∧
                b * x / ((r : ℝ) * outsideSlotProduct C.bands z s) ≤
                    Real.exp (C.bands.c₂ * C.bands.scale x 0)

end Erdos821.P7Core
