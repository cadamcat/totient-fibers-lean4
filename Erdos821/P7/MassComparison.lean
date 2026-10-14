import Erdos821.P7.WindowAverage

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem normalize_mass_comparison (N R S P X mass c kmin kmax k M : ℝ)
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hP : 0 ≤ P) (hX : 0 ≤ X)
    (hc : 0 < c) (hmin : 0 < kmin) (hmax : 0 < kmax)
    (hk : 0 < k) (hM : 0 < M) (hslot : k ≤ S ∧ S ≤ M)
    (hlower : N * (c * R) * ((kmin * X) * (P / 2)) ≤ mass)
    (hupper : mass ≤ N * R * (kmax * X) * P) :
    (c * kmin / (2 * M)) * X * (N * R * S) * P ≤ mass ∧
      mass ≤ (kmax / k) * X * (N * R * S) * P := by
  constructor
  · apply le_trans _ hlower
    calc
      _ = (N * R * c * kmin * X * P / 2) * (S / M) := by ring
      _ ≤ (N * R * c * kmin * X * P / 2) * 1 := by
        apply mul_le_mul_of_nonneg_left ((div_le_one hM).mpr hslot.2)
        positivity
      _ = _ := by ring
  · apply le_trans hupper
    calc
      _ = (N * R * kmax * X * P) * 1 := by ring
      _ ≤ (N * R * kmax * X * P) * (S / k) := by
        apply mul_le_mul_of_nonneg_left ((one_le_div hk).mpr hslot.1)
        positivity
      _ = _ := by ring

/-- The remaining analytic helper inputs imply the two-sided candidate
mass comparison. All comparison constants are chosen before jstar. -/
theorem candidate_mass_comparison_of_tasks
    (hwindow : FreeWindowBoundsTask) (hprime : PrimeWindowHarmonicTask)
    (hplace : CandidatePlacementTask) (hprefix : PrefixHarmonicTask)
    (hc : ClassicalInputs) (δ : ℝ) (C : CandidateData) (hC : C.Geometry δ) :
    ∃ cmin cmax : ℝ, 0 < cmin ∧ 0 < cmax ∧
      ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
        cmin * (x / L x) * C.bands.harmonicQ x jstar * C.bands.harmonicP x ≤
          C.mass x jstar ∧
        C.mass x jstar ≤
          cmax * (x / L x) * C.bands.harmonicQ x jstar * C.bands.harmonicP x := by
  obtain ⟨epsilon, sigma, kmin, kmax, heps, hepslt, hsigma, hmin, hmax, hwin⟩ :=
    hwindow hprime hplace hc δ C hC
  obtain ⟨c, hcp, hpre⟩ := hprefix hc δ C hC epsilon heps hepslt
  obtain ⟨k, M, hk, hM, hslot⟩ := free_slot_harmonic_bounds hc C δ hC
  obtain ⟨_, hsum⟩ := harmonicP_summable_polylog C.bands hC.1
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hpsi : Function.support C.psi ⊆ Set.Icc 1 2 := by
    rcases hC with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hp, _, _⟩
    exact hp
  have hpsi0 : ∀ y, 0 ≤ C.psi y := by
    rcases hC with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hp, _⟩
    exact hp
  refine ⟨c * kmin / (2 * M), kmax / k, by positivity, by positivity, ?_⟩
  intro jstar hj
  filter_upwards [hwin jstar hj, hpre jstar hj, hslot, hsum,
    geometry_harmonicP_small_mass C δ hC sigma hsigma,
    eventually_candidate_mass_free_window C δ hC, eventually_gt_atTop 0,
    Erdos821.S56Core.tendsto_L.eventually (eventually_gt_atTop 0)]
    with x hw hp hs hPsum hhead hmass hx hL
  let s : C.bands.Slot x := (⟨0, Nat.zero_lt_succ _⟩, ⟨0, hC.1.1⟩)
  have hs0 : s.1.val = 0 := rfl
  have hs1 : s.2.val = 0 := rfl
  have hS := hs jstar hj s hs0
  have hrest := prefix_fraction_rest C epsilon c x jstar s (hk.trans_le hS.1)
    (hp s hs0 hs1)
  have hupper := mass_rest_upper C hpsi x hx jstar s (kmax * (x / L x))
    hPsum.1 (hmass jstar s) (fun z r hr => (hw s hs0 hs1 z r hr).1)
  have hlower := mass_rest_lower C hpsi hpsi0 x hx jstar s epsilon c
    (kmin * (x / L x)) (x ^ sigma) (by positivity) hPsum.1 (hmass jstar s)
    hrest hhead (fun z hz r hr hsmall => (hw s hs0 hs1 z r hr).2 hz hsmall)
  have hR : 0 ≤ restHarmonic C.bands x jstar s := by
    apply Finset.sum_nonneg
    intro z _
    positivity
  have hP : 0 ≤ C.bands.harmonicP x := tsum_nonneg (groupHarmonicTerm_nonneg _ _)
  have hcomp := normalize_mass_comparison
    (((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹)
    (restHarmonic C.bands x jstar s) (slotHarmonic C.bands x jstar s)
    (C.bands.harmonicP x) (x / L x) (C.mass x jstar) c kmin kmax k M
    (by positivity) hR hP (by positivity) hcp hmin hmax hk hMpos hS hlower hupper
  simpa only [← harmonicQ_free_split C.bands x jstar s] using hcomp

end Erdos821.P7Core

