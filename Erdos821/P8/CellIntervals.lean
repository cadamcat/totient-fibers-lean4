import Erdos821.P8.MellinVariation
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma logIndex_mono {delta : ℝ} (hdelta : 0 < delta) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) : logIndex delta m ≤ logIndex delta n := by
  unfold logIndex
  apply sub_le_sub_right
  apply Int.ceil_mono
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn)) hdelta.le

lemma exp_sub_one_le_two_mul {delta : ℝ} (hdelta : 0 ≤ delta) (hle : delta ≤ 1) :
    Real.exp delta - 1 ≤ 2 * delta := by
  have harg : ‖(delta : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdelta] using hle
  have he := Complex.norm_exp_sub_one_le harg
  have hnonneg : 0 ≤ Real.exp delta - 1 := sub_nonneg.mpr (Real.one_le_exp hdelta)
  simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg hdelta] using he

lemma logCellAt_card_le (delta : ℝ) (j : ℤ) (hdelta : 0 ≤ delta) :
    ((logCellAt delta j).card : ℝ) ≤
      Real.exp ((j : ℝ) * delta) * (Real.exp delta - 1) + 1 := by
  let Y := Real.exp ((j : ℝ) * delta)
  let Z := Real.exp (((j : ℝ) + 1) * delta)
  have hYZ : Y ≤ Z := by dsimp [Y, Z]; apply Real.exp_le_exp.mpr; nlinarith
  have hfloor : ⌊Y⌋₊ ≤ ⌊Z⌋₊ := Nat.floor_mono hYZ
  have hY := Nat.lt_floor_add_one Y
  have hZ := Nat.floor_le (Real.exp_pos (((j : ℝ) + 1) * delta)).le
  have heq : Z = Y * Real.exp delta := by
    dsimp [Y, Z]
    rw [add_mul, one_mul, Real.exp_add]
  change ((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).card : ℝ) ≤ _
  rw [Nat.card_Ioc, Nat.cast_sub hfloor]
  change (⌊Z⌋₊ : ℝ) - (⌊Y⌋₊ : ℝ) ≤ Y * (Real.exp delta - 1) + 1
  nlinarith

lemma logCellAt_harmonic_mass_le {delta : ℝ} (hdelta : 0 < delta) (j : ℤ) :
    (∑ m ∈ logCellAt delta j, (m : ℝ)⁻¹) ≤
      Real.exp delta - 1 + (Real.exp ((j : ℝ) * delta))⁻¹ := by
  let Y := Real.exp ((j : ℝ) * delta)
  have hY : 0 < Y := Real.exp_pos _
  calc
    (∑ m ∈ logCellAt delta j, (m : ℝ)⁻¹) ≤
        ∑ _m ∈ logCellAt delta j, Y⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      rcases (mem_logCellAt_iff delta j m).mp hm with ⟨hm0, hmlo, _⟩
      have hYm : Y < (m : ℝ) :=
        (Real.lt_log_iff_exp_lt (by exact_mod_cast hm0)).mp hmlo
      exact inv_anti₀ hY hYm.le
    _ = ((logCellAt delta j).card : ℝ) * Y⁻¹ := by simp
    _ ≤ (Y * (Real.exp delta - 1) + 1) * Y⁻¹ :=
      mul_le_mul_of_nonneg_right (logCellAt_card_le delta j hdelta.le) (by positivity)
    _ = Real.exp delta - 1 + Y⁻¹ := by field_simp

lemma logCellAt_lower_inv_le {delta : ℝ} (j : ℤ) {n : ℕ}
    (hn : n ∈ logCellAt delta j) :
    (Real.exp ((j : ℝ) * delta))⁻¹ ≤ Real.exp delta / (n : ℝ) := by
  rcases (mem_logCellAt_iff delta j n).mp hn with ⟨hn0, _, hnhi⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hnexp := (Real.log_le_iff_le_exp hnpos).mp hnhi
  have heq : Real.exp (((j : ℝ) + 1) * delta) =
      Real.exp ((j : ℝ) * delta) * Real.exp delta := by
    rw [add_mul, one_mul, Real.exp_add]
  rw [heq] at hnexp
  apply (le_div_iff₀ hnpos).mpr
  exact (inv_mul_le_iff₀ (Real.exp_pos _)).mpr hnexp

/-- An endpoint cell contributes its logarithmic width and one integer-count error. -/
theorem logCellAt_harmonic_mass_endpoint {delta : ℝ} (hdelta : 0 < delta)
    (hle : delta ≤ 1) (j : ℤ) {n : ℕ} (hn : n ∈ logCellAt delta j) :
    (∑ m ∈ logCellAt delta j, (m : ℝ)⁻¹) ≤ 2 * delta + Real.exp 1 / (n : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast ((mem_logCellAt_iff delta j n).mp hn).1
  calc
    (∑ m ∈ logCellAt delta j, (m : ℝ)⁻¹) ≤
        Real.exp delta - 1 + (Real.exp ((j : ℝ) * delta))⁻¹ :=
      logCellAt_harmonic_mass_le hdelta j
    _ ≤ 2 * delta + Real.exp delta / (n : ℝ) :=
      add_le_add (exp_sub_one_le_two_mul hdelta.le hle) (logCellAt_lower_inv_le j hn)
    _ ≤ 2 * delta + Real.exp 1 / (n : ℝ) := by
      gcongr

theorem logCell_harmonic_mass_endpoint {x : ℝ} (hx : 1 < x) (S : ℝ)
    (hle : L x ^ (-S) ≤ 1) {n : ℕ} (hn : 0 < n) :
    (∑ m ∈ logCell x S n, (m : ℝ)⁻¹) ≤
      2 * L x ^ (-S) + Real.exp 1 / (n : ℝ) := by
  rw [logCell_eq_index]
  exact logCellAt_harmonic_mass_endpoint (cell_width_pos hx S) hle _
    (mem_assigned_logCell (cell_width_pos hx S) hn)

lemma logCellAt_subset_Icc_of_interior {delta : ℝ} (hdelta : 0 < delta)
    {a b : ℕ} (_ha : 0 < a) {j : ℤ}
    (hleft : logIndex delta a < j) (hright : j < logIndex delta b) :
    logCellAt delta j ⊆ Finset.Icc a b := by
  intro m hm
  have hm0 := ((mem_logCellAt_iff delta j m).mp hm).1
  have hmj := logIndex_eq_of_mem hdelta hm
  rw [Finset.mem_Icc]
  constructor
  · by_contra h
    have hma : m ≤ a := (Nat.lt_of_not_ge h).le
    have := logIndex_mono hdelta hm0 hma
    omega
  · by_contra h
    have hbm : b ≤ m := (Nat.lt_of_not_ge h).le
    have hb0 : 0 < b := by
      by_contra hb
      have hbz : b = 0 := by omega
      have hba : logIndex delta b ≤ logIndex delta a := by
        simp only [hbz, logIndex, Nat.cast_zero, Real.log_zero, zero_div]
        apply sub_le_sub_right
        exact Int.ceil_mono (div_nonneg (Real.log_natCast_nonneg a) hdelta.le)
      omega
    have := logIndex_mono hdelta hb0 hbm
    omega

lemma interval_logIndex_fiber_subset {delta : ℝ} (hdelta : 0 < delta)
    {a b : ℕ} (ha : 0 < a) (j : ℤ) :
    ((Finset.Icc a b).filter (fun m => logIndex delta m = j)) ⊆ logCellAt delta j := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hm, hmj⟩
  have hm0 : 0 < m := ha.trans_le (Finset.mem_Icc.mp hm).1
  simpa only [hmj] using mem_assigned_logCell hdelta hm0

lemma interval_logIndex_fiber_eq_of_interior {delta : ℝ} (hdelta : 0 < delta)
    {a b : ℕ} (ha : 0 < a) {j : ℤ}
    (hleft : logIndex delta a < j) (hright : j < logIndex delta b) :
    ((Finset.Icc a b).filter (fun m => logIndex delta m = j)) = logCellAt delta j := by
  apply Finset.Subset.antisymm (interval_logIndex_fiber_subset hdelta ha j)
  intro m hm
  exact Finset.mem_filter.mpr ⟨logCellAt_subset_Icc_of_interior hdelta ha hleft hright hm,
    logIndex_eq_of_mem hdelta hm⟩

lemma interval_sum_by_logIndex {M : Type*} [AddCommMonoid M]
    (delta : ℝ) (a b : ℕ) (f : ℕ → M) :
    (∑ j ∈ (Finset.Icc a b).image (logIndex delta),
      ∑ m ∈ (Finset.Icc a b).filter (fun m => logIndex delta m = j), f m) =
      ∑ m ∈ Finset.Icc a b, f m :=
  Finset.sum_fiberwise_of_maps_to (fun _m hm => Finset.mem_image_of_mem _ hm) f

lemma harmonic_mass_nonneg (s : Finset ℕ) : 0 ≤ ∑ m ∈ s, (m : ℝ)⁻¹ :=
  Finset.sum_nonneg (fun m _ => inv_nonneg.mpr (Nat.cast_nonneg m))

/-- Grouping an interval by logarithmic index leaves at most two partial cells. -/
theorem norm_interval_sum_le_full_cells_and_endpoints {delta M : ℝ}
    (hdelta : 0 < delta) (hM : 0 ≤ M) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (c : ℕ → ℂ)
    (hpoint : ∀ m ∈ Finset.Icc a b, ‖c m‖ ≤ (m : ℝ)⁻¹)
    (hfull : ∀ j : ℤ, logIndex delta a < j → j < logIndex delta b →
      ‖∑ m ∈ logCellAt delta j, c m‖ ≤ M * (∑ m ∈ logCellAt delta j, (m : ℝ)⁻¹)) :
    ‖∑ m ∈ Finset.Icc a b, c m‖ ≤ M * (∑ m ∈ Finset.Icc a b, (m : ℝ)⁻¹) +
      (∑ m ∈ logCellAt delta (logIndex delta a), (m : ℝ)⁻¹) +
      (∑ m ∈ logCellAt delta (logIndex delta b), (m : ℝ)⁻¹) := by
  let s := Finset.Icc a b
  let t := s.image (logIndex delta)
  let fiber := fun j => s.filter (fun m => logIndex delta m = j)
  let H := fun j => ∑ m ∈ logCellAt delta j, (m : ℝ)⁻¹
  let E := fun j => (if j = logIndex delta a then H (logIndex delta a) else 0) +
    (if j = logIndex delta b then H (logIndex delta b) else 0)
  have hA : logIndex delta a ∈ t :=
    Finset.mem_image_of_mem _ (Finset.left_mem_Icc.mpr hab)
  have hB : logIndex delta b ∈ t :=
    Finset.mem_image_of_mem _ (Finset.right_mem_Icc.mpr hab)
  have hbound : ∀ j ∈ t, ‖∑ m ∈ fiber j, c m‖ ≤
      M * (∑ m ∈ fiber j, (m : ℝ)⁻¹) + E j := by
    intro j hj
    have hs := interval_logIndex_fiber_subset (b := b) hdelta ha j
    have hmass : (∑ m ∈ fiber j, (m : ℝ)⁻¹) ≤ H j :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => by positivity)
    have hnorm : ‖∑ m ∈ fiber j, c m‖ ≤ ∑ m ∈ fiber j, (m : ℝ)⁻¹ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun m hm => hpoint m (Finset.mem_filter.mp hm).1)
    have hMmass : 0 ≤ M * (∑ m ∈ fiber j, (m : ℝ)⁻¹) :=
      mul_nonneg hM (harmonic_mass_nonneg _)
    by_cases hja : j = logIndex delta a
    · have hE : H j ≤ E j := by
        dsimp only [E]
        rw [if_pos hja, hja]
        exact le_add_of_nonneg_right (by split_ifs <;> first | exact harmonic_mass_nonneg _ | positivity)
      exact (hnorm.trans hmass).trans (hE.trans (le_add_of_nonneg_left hMmass))
    by_cases hjb : j = logIndex delta b
    · have hE : H j ≤ E j := by
        dsimp only [E]
        rw [if_pos hjb, hjb]
        exact le_add_of_nonneg_left (by split_ifs <;> first | exact harmonic_mass_nonneg _ | positivity)
      exact (hnorm.trans hmass).trans (hE.trans (le_add_of_nonneg_left hMmass))
    · rcases Finset.mem_image.mp hj with ⟨n, hn, hnj⟩
      have hnab := Finset.mem_Icc.mp hn
      have hn0 := ha.trans_le hnab.1
      have hleft : logIndex delta a < j := by
        have := logIndex_mono hdelta ha hnab.1
        omega
      have hright : j < logIndex delta b := by
        have := logIndex_mono hdelta hn0 hnab.2
        omega
      have hf : fiber j = logCellAt delta j :=
        interval_logIndex_fiber_eq_of_interior hdelta ha hleft hright
      simpa only [hf, E, hja, hjb, ite_false, add_zero] using hfull j hleft hright
  calc
    ‖∑ m ∈ Finset.Icc a b, c m‖ = ‖∑ j ∈ t, ∑ m ∈ fiber j, c m‖ := by
      rw [interval_sum_by_logIndex]
    _ ≤ ∑ j ∈ t, ‖∑ m ∈ fiber j, c m‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ t, (M * (∑ m ∈ fiber j, (m : ℝ)⁻¹) + E j) :=
      Finset.sum_le_sum hbound
    _ = M * (∑ m ∈ Finset.Icc a b, (m : ℝ)⁻¹) + H (logIndex delta a) +
        H (logIndex delta b) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      change M * (∑ j ∈ t, ∑ m ∈ fiber j, (m : ℝ)⁻¹) + _ = _
      rw [interval_sum_by_logIndex]
      simp only [E, Finset.sum_add_distrib, Finset.sum_ite_eq', hA, hB, ite_true]
      ring

theorem norm_interval_sum_le_with_endpoint_mass {delta M : ℝ}
    (hdelta : 0 < delta) (hle : delta ≤ 1) (hM : 0 ≤ M)
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (c : ℕ → ℂ)
    (hpoint : ∀ m ∈ Finset.Icc a b, ‖c m‖ ≤ (m : ℝ)⁻¹)
    (hfull : ∀ j : ℤ, logIndex delta a < j → j < logIndex delta b →
      ‖∑ m ∈ logCellAt delta j, c m‖ ≤ M * (∑ m ∈ logCellAt delta j, (m : ℝ)⁻¹)) :
    ‖∑ m ∈ Finset.Icc a b, c m‖ ≤ M * (∑ m ∈ Finset.Icc a b, (m : ℝ)⁻¹) +
      4 * delta + 2 * Real.exp 1 / (a : ℝ) := by
  have hb : 0 < b := ha.trans_le hab
  have hA := logCellAt_harmonic_mass_endpoint hdelta hle _ (mem_assigned_logCell hdelta ha)
  have hB := logCellAt_harmonic_mass_endpoint hdelta hle _ (mem_assigned_logCell hdelta hb)
  have hdiv : Real.exp 1 / (b : ℝ) ≤ Real.exp 1 / (a : ℝ) := by
    gcongr
  have hsum := norm_interval_sum_le_full_cells_and_endpoints hdelta hM ha hab c hpoint hfull
  simp only [mul_div_assoc]
  linarith

theorem norm_proxy_interval_mellin_le (I : FactorTest) {x : ℝ} (hx : 1 < x)
    (S u : ℝ) (hle : L x ^ (-S) ≤ 1)
    (hsmall : (1 + |u|) * L x ^ (-S) ≤ 1)
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hden : ∀ n ∈ Finset.Icc a b, 0 < proxyDenominator x S n)
    (hsubset : ∀ n ∈ Finset.Icc a b, ∀ m ∈ logCell x S n,
      test I x m ≠ 0 → rough (W x) m) :
    ‖∑ m ∈ Finset.Icc a b, ((test I x m - proxy I x S m : ℝ) : ℂ) *
      mellin m u / (m : ℂ)‖ ≤
      2 * (1 + |u|) * L x ^ (-S) * (∑ m ∈ Finset.Icc a b, (m : ℝ)⁻¹) +
      4 * L x ^ (-S) + 2 * Real.exp 1 / (a : ℝ) := by
  apply norm_interval_sum_le_with_endpoint_mass (M := 2 * (1 + |u|) * L x ^ (-S))
    (cell_width_pos hx S) hle
    (mul_nonneg (by positivity) (cell_width_pos hx S).le) ha hab
  · intro m hm
    have hm0 := ha.trans_le (Finset.mem_Icc.mp hm).1
    have hc := norm_cell_difference_le_one I hx S m (hden m hm) (hsubset m hm)
      (mem_logCell_self hx S hm0)
    have hw : ‖mellin m u / (m : ℂ)‖ = (m : ℝ)⁻¹ := by
      simpa only [mellinWeight, Complex.ofReal_natCast] using
        norm_mellinWeight (by exact_mod_cast hm0 : 0 < (m : ℝ)) u
    rw [mul_div_assoc, norm_mul, hw]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (by positivity)
  · intro j hleft hright
    by_cases hne : (logCellAt (L x ^ (-S)) j).Nonempty
    · rcases hne with ⟨n, hn⟩
      have hnab := logCellAt_subset_Icc_of_interior (cell_width_pos hx S) ha hleft hright hn
      have hn0 := ha.trans_le (Finset.mem_Icc.mp hnab).1
      have heq : logCell x S n = logCellAt (L x ^ (-S)) j := by
        rw [logCell_eq_index, logIndex_eq_of_mem (cell_width_pos hx S) hn]
      simpa only [heq] using norm_proxy_full_cell_mellin_le I hx S u n hn0
        (hden n hnab) (hsubset n hnab) hsmall
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, norm_zero,
        mul_zero, le_refl]

lemma interval_harmonic_mass_le_log {a b : ℕ} (ha : 0 < a) :
    (∑ m ∈ Finset.Icc a b, (m : ℝ)⁻¹) ≤ 1 + Real.log b := by
  have hs : Finset.Icc a b ⊆ Finset.Icc 1 b := by
    intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨ham, hmb⟩
    exact Finset.mem_Icc.mpr ⟨(by omega), hmb⟩
  calc
    (∑ m ∈ Finset.Icc a b, (m : ℝ)⁻¹) ≤ ∑ m ∈ Finset.Icc 1 b, (m : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => by positivity)
    _ = (harmonic b : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log b := harmonic_le_one_add_log b

lemma interval_harmonic_mass_le_probe {x : ℝ} (hx : 1 < x) {a b : ℕ}
    (ha : 0 < a) (hb : (b : ℝ) ≤ x ^ (2 : ℕ)) :
    (∑ m ∈ Finset.Icc a b, (m : ℝ)⁻¹) ≤ 1 + 2 * L x := by
  by_cases hb0 : b = 0
  · simp only [hb0, Finset.Icc_eq_empty_of_lt (by omega : 0 < a), Finset.sum_empty]
    have : 0 < L x := Real.log_pos hx
    positivity
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hb0)
  apply (interval_harmonic_mass_le_log ha).trans
  have hlog := Real.log_le_log hbpos hb
  simpa only [Real.log_pow, Nat.cast_ofNat, L] using add_le_add_right hlog 1

end Erdos821.P8Core

