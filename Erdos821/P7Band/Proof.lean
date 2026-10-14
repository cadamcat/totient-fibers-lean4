import Erdos821.P7Band.Geometry

/-! Proof of `Erdos821.P7Core.BandGeometryTask`: the explicit prime-band family. -/

noncomputable section
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Band
open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

/-- The fixed candidate geometry. -/
def geom : Geometry where
  a := 1 / 10
  b := 1 / 5
  c := 3 / 10
  d := 2 / 5
  c₀ := 1 / 40
  C₀ := 1 / 20
  vmin := Real.log (6 / 5) / 2
  vmax := 2 * Real.log (6 / 5)
  q := 1 / 2
  ell := 1
  ordered := by norm_num
  positive := by
    have := Real.log_pos (show (1 : ℝ) < 6 / 5 by norm_num)
    exact ⟨by norm_num, by norm_num, by positivity, by linarith⟩
  damping := by norm_num
  marks := le_rfl

/-- The band family for a given `r₀`. -/
def bandData (r₀ : ℕ) : BandData where
  geometry := geom
  groups := groups (1 / ((r₀ : ℝ) * (1 + 6 / 5)))
  r₀ := r₀
  c₁ := 1
  c₂ := 6 / 5
  s' := 1 / ((r₀ : ℝ) * (1 + 6 / 5))
  ratio := 2
  last := P7Core.lastBand (1 / ((r₀ : ℝ) * (1 + 6 / 5)))

theorem band_mem {D : BandData} (hc₁ : D.c₁ = 1) (hc₂ : D.c₂ = 6 / 5) (hratio : D.ratio = 2)
    {x : ℝ} {j p : ℕ} (hp : p ∈ D.band x j) :
    Real.exp (D.s' * L x / 2 ^ j) ≤ p ∧ (p : ℝ) ≤ Real.exp (6 / 5 * (D.s' * L x / 2 ^ j)) := by
  simp only [BandData.band, BandData.scale, hc₁, hc₂, hratio, one_mul, Finset.mem_filter,
    Finset.mem_Icc] at hp
  exact ⟨Nat.ceil_le.mp hp.1.1, (Nat.le_floor_iff (Real.exp_pos _).le).mp hp.1.2⟩

theorem admissible_of {s x : ℝ} (h : good s x) (hT : 40 ≤ T x) {Y : ℝ}
    (hYmass : ∀ b : ℝ, 0 < b → Y ≤ Real.exp (3 / 2 * b) →
      Real.log (6 / 5) / 2 ≤ ∑ p ∈ grp b, 1 / (p : ℝ) ∧
        ∑ p ∈ grp b, 1 / (p : ℝ) ≤ 2 * Real.log (6 / 5))
    (hY : Y ≤ L x ^ (1 / 10 : ℝ)) :
    Admissible geom x (mkGroups s x h) := by
  have hL : 1 < L x := h.1
  have hL0 : 0 < L x := by linarith
  have hcount : (1 / 40 : ℝ) * T x ≤ (nG x : ℝ) ∧ (nG x : ℝ) ≤ 1 / 20 * T x := by
    have h1 := Nat.lt_floor_add_one (T x / 20)
    have h2 := Nat.floor_le (show 0 ≤ T x / 20 by linarith)
    simp only [nG]
    constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change _ ≤ ((smallSet (nG x)).card : ℝ) ∧ ((smallSet (nG x)).card : ℝ) ≤ _
    rw [card_smallSet]; exact hcount
  · change _ ≤ ((Finset.univ \ smallSet (nG x)).card : ℝ) ∧
      ((Finset.univ \ smallSet (nG x)).card : ℝ) ≤ _
    rw [card_bigSet]; exact hcount
  · intro g
    have rg := idx_range h g
    have hlow : L x ^ (1 / 10 : ℝ) ≤ 3 / 2 * ex s x (idx s x g) := by
      split_ifs at rg with hg
      · exact rg.1
      · exact (Real.rpow_le_rpow_of_exponent_le hL.le (by norm_num)).trans rg.1
    have hpos : 0 < ex s x (idx s x g) := by
      have := Real.rpow_pos_of_pos hL0 (1 / 10 : ℝ); linarith
    have hYb : Y ≤ Real.exp (3 / 2 * ex s x (idx s x g)) := by
      have := Real.add_one_le_exp (3 / 2 * ex s x (idx s x g))
      linarith
    exact hYmass _ hpos hYb
  · intro g p hp
    have rg := idx_range h g
    change p ∈ grp (ex s x (idx s x g)) at hp
    obtain ⟨-, h1, h2⟩ := mem_grp.mp hp
    by_cases hg : (g : ℕ) < nG x
    · have hm : g ∈ (mkGroups s x h).small := mem_smallSet.mpr hg
      simp only [hm, hg, ↓reduceIte] at rg ⊢
      exact ⟨(Real.exp_le_exp.mpr rg.1).trans h1.le, h2.trans (Real.exp_le_exp.mpr rg.2)⟩
    · have hm : g ∉ (mkGroups s x h).small := fun h' => hg (mem_smallSet.mp h')
      simp only [hm, hg, ↓reduceIte] at rg ⊢
      exact ⟨(Real.exp_le_exp.mpr rg.1).trans h1.le, h2.trans (Real.exp_le_exp.mpr rg.2)⟩
  · intro g _
    refine ⟨((⌊Real.exp (3 / 2 * ex s x (idx s x g))⌋₊ + 1 : ℕ) : ℝ),
      Real.exp (9 / 5 * ex s x (idx s x g)), fun p => ?_⟩
    change p ∈ grp (ex s x (idx s x g)) ↔ _
    rw [mem_grp, Nat.cast_le, Nat.add_one_le_iff, Nat.floor_lt (Real.exp_pos _).le]

theorem _root_.Erdos821.P7Core.BandGeometryTask_proof : Erdos821.P7Core.BandGeometryTask := by
  intro r₀ hr₀
  set s : ℝ := 1 / ((r₀ : ℝ) * (1 + 6 / 5)) with hs_def
  have hr : (6 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hs : 0 < s := by positivity
  have hlast := P7Core.lastBand_scale_bounds s hs
  refine ⟨bandData r₀, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · obtain ⟨Y, hYmass⟩ := grp_mass_eventually
    have hY : ∀ᶠ x : ℝ in atTop, Y ≤ L x ^ (1 / 10 : ℝ) :=
      ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop).eventually_ge_atTop Y
    have hc₂s : (6 / 5 : ℝ) * s < 1 / 4 := by
      have hpos : 0 < (r₀ : ℝ) * (1 + 6 / 5) := by positivity
      have : (6 / 5 : ℝ) * s = (6 / 5) / ((r₀ : ℝ) * (1 + 6 / 5)) := by rw [hs_def]; ring
      rw [this, div_lt_iff₀ hpos]
      linarith
    refine ⟨show 1 ≤ r₀ by omega, show (0 : ℝ) < 1 by norm_num,
      show (1 : ℝ) < 6 / 5 by norm_num, hs, show (1 : ℝ) < 2 by norm_num, hc₂s,
      show ((r₀ : ℝ) - 1) * 1 / 2 ≥ 6 / 5 + 1 by linarith,
      P7Core.lastBand_tendsto s hs, 20, 40, by norm_num, by norm_num, ?_⟩
    filter_upwards [eventually_good hs, T_tendsto.eventually_ge_atTop 40, hY, hlast,
      Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hg hT hYx hl hL
    have hu : 0 < s * L x := mul_pos hs (by change 0 < Real.log x; linarith)
    have hadm := admissible_of hg hT hYmass hYx
    rw [← groups_eq hg] at hadm
    have hbg : ∀ j : ℕ, ∀ g : Fin (groups s x).size,
        Disjoint ((bandData r₀).band x j) ((groups s x).primes g) := by
      rw [groups_eq hg]
      intro j g
      refine Finset.disjoint_left.mpr fun p hp hq => ?_
      obtain ⟨h1, h2⟩ := band_mem (D := bandData r₀) rfl rfl rfl hp
      exact band_grp_disjoint hu j (idx s x g) h1 h2 hq
    exact ⟨hadm, hl.1, hl.2.2.le,
      fun i _ j _ hij => P7Core.bands_disjoint (bandData r₀) x rfl rfl rfl hu i j hij,
      fun j _ g => hbg j g⟩
  · filter_upwards [hlast] with x hl
    refine ⟨?_, ?_⟩
    · rw [show (bandData r₀).c₁ = 1 from rfl, one_mul]; exact hl.1
    · rw [show (bandData r₀).c₁ = 1 from rfl, one_mul]; exact hl.2.1

end Erdos821.P7Band

/-- The owned blueprint goal follows. -/
example : Erdos821.Blueprint.candidate_geometry_statement :=
  Erdos821.P7Core.candidateGeometryTask_closes Erdos821.P7Core.BandGeometryTask_proof
