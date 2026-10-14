import Erdos821.S56.GroupParts
import Erdos821.S56.BandSize

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Every group prime lies below the compulsory roughness threshold. -/
theorem group_primes_lt_W (P : Geometry) :
    ∀ᶠ x : ℝ in atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ p ∈ groupPrimes G, (p : ℝ) < W x := by
  filter_upwards [tendsto_L.eventually (eventually_gt_atTop 1)] with x hL
  intro G hG p hp
  obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hs, hb, hm, hpr, hi⟩ := hG
  have hpd : (p : ℝ) ≤ Real.exp (L x ^ P.d) := by
    have h := hpr g p hpg
    split_ifs at h
    · have hbd : P.b < P.d := P.ordered.2.2.1.trans P.ordered.2.2.2.1
      have hpow := Real.rpow_le_rpow_of_exponent_le hL.le hbd.le
      exact h.2.trans (Real.exp_le_exp.mpr hpow)
    · exact h.2
  have hd : P.d < (1 / 2 : ℝ) := by linarith [P.ordered.2.2.2.2]
  have hroot : L x ^ P.d < Real.sqrt (L x) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_lt_rpow_of_exponent_lt hL hd
  exact hpd.trans_lt (Real.exp_lt_exp.mpr hroot)

theorem rough_groupFree (G : PrimeGroups) (x : ℝ) (n : ℕ)
    (hg : ∀ p ∈ groupPrimes G, (p : ℝ) < W x) (hn : rough (W x) n) :
    GroupFree G n := by
  intro p hp hdvd
  obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
  exact (not_lt_of_ge (hg p hp).le) (hn.2 p (G.prime g p hpg) hdvd)

theorem eventually_rough_groupFree (P : Geometry) :
    ∀ᶠ x : ℝ in atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ n : ℕ, rough (W x) n → GroupFree G n := by
  filter_upwards [group_primes_lt_W P] with x hx
  intro G hG n hn
  exact rough_groupFree G x n (hx G hG) hn


end Erdos821.S56Core
