import Erdos821.P8.ProxyDenominator

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma natCast_eq_residue {r : ℕ} [NeZero r] (n : ℕ) (a : ZMod r) :
    (n : ZMod r) = a ↔ n % r = a.val % r := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  exact ZMod.natCast_eq_natCast_iff' n a.val r

lemma rough_character_sum_by_residue (s : Finset ℕ) (y : ℝ) {r : ℕ} [NeZero r]
    (chi : DirichletCharacter ℂ r) :
    (∑ n ∈ s.filter (rough y), chi (n : ZMod r)) =
      ∑ a : ZMod r, chi a *
        (((s.filter (fun n => rough y n ∧ n % r = a.val % r)).card : ℕ) : ℂ) := by
  rw [← Finset.sum_fiberwise (s.filter (rough y)) (fun n => (n : ZMod r))]
  apply Finset.sum_congr rfl
  intro a _
  have hf : (s.filter (rough y)).filter (fun n : ℕ => (n : ZMod r) = a) =
      s.filter (fun n => rough y n ∧ n % r = a.val % r) := by
    ext n
    simp only [Finset.mem_filter, natCast_eq_residue]
    tauto
  calc
    (∑ n ∈ (s.filter (rough y)).filter (fun n : ℕ => (n : ZMod r) = a), chi (n : ZMod r)) =
        ∑ _n ∈ (s.filter (rough y)).filter (fun n : ℕ => (n : ZMod r) = a), chi a := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [(Finset.mem_filter.mp hn).2]
    _ = _ := by simp [hf, mul_comm]

/-- Equal main terms disappear when summed against a nonprincipal character. -/
theorem norm_rough_character_sum_le_residue_error (s : Finset ℕ) (y : ℝ)
    {r : ℕ} [NeZero r] (chi : DirichletCharacter ℂ r) (hchi : chi ≠ 1)
    (main error : ℝ) (herror : 0 ≤ error)
    (hcounts : ∀ a : ZMod r, Nat.Coprime a.val r →
      |(((s.filter (fun n => rough y n ∧ n % r = a.val % r)).card : ℕ) : ℝ) - main| ≤ error) :
    ‖∑ n ∈ s.filter (rough y), chi (n : ZMod r)‖ ≤ (r : ℝ) * error := by
  let counts : ZMod r → ℝ := fun a =>
    ((s.filter (fun n => rough y n ∧ n % r = a.val % r)).card : ℝ)
  have hzero : (∑ a : ZMod r, chi a) = 0 := MulChar.sum_eq_zero_of_ne_one hchi
  have hcenter : (∑ a : ZMod r, chi a * (counts a : ℂ)) =
      ∑ a : ZMod r, chi a * ((counts a - main : ℝ) : ℂ) := by
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
  rw [rough_character_sum_by_residue]
  change ‖∑ a : ZMod r, chi a * (counts a : ℂ)‖ ≤ _
  rw [hcenter]
  calc
    ‖∑ a : ZMod r, chi a * ((counts a - main : ℝ) : ℂ)‖ ≤
        ∑ a : ZMod r, ‖chi a * ((counts a - main : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ZMod r, error := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : IsUnit a
      · have hcop : Nat.Coprime a.val r := by
          apply (ZMod.isUnit_iff_coprime a.val r).mp
          simpa only [ZMod.natCast_zmod_val] using ha
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        simpa only [one_mul] using mul_le_mul (chi.norm_le_one a) (hcounts a hcop)
          (abs_nonneg _) (by norm_num)
      · rw [chi.map_nonunit ha, zero_mul, norm_zero]
        exact herror
    _ = (r : ℝ) * error := by simp [ZMod.card]

theorem eventually_rough_character_interval_bound (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b C B A eta : ℝ)
    (hb : 0 < b) (hC : 0 < C) (hB : 0 < B) (hA : 0 < A) (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, ∀ (lo hi : ℝ) (r : ℕ) (chi : DirichletCharacter ℂ r),
      x ^ b ≤ lo → lo ≤ hi → hi ≤ x ^ C →
      1 ≤ r → (r : ℝ) ≤ L x ^ B → chi ≠ 1 →
      ‖∑ n ∈ (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter (rough (W x)), chi (n : ZMod r)‖ ≤
        (r : ℝ) * ((hi - lo) * sieveProduct (W x) / (Nat.totient r : ℝ) * L x ^ (-A) +
          x ^ eta) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hresidue hc hs b C B A eta hb hC hB hA heta] with x hx hcount
  intro lo hi r chi hlo horder hhi hr hrB hchi
  letI : NeZero r := ⟨by omega⟩
  apply norm_rough_character_sum_le_residue_error _ _ chi hchi
    ((hi - lo) * sieveProduct (W x) / (Nat.totient r : ℝ))
  · have hlength : 0 ≤ hi - lo := sub_nonneg.mpr horder
    have hL : 0 < L x := Real.log_pos hx
    have hV : 0 < sieveProduct (W x) := sieveProduct_pos _
    have hx0 : 0 < x := by linarith
    positivity
  · intro a ha
    exact hcount lo hi r a.val hlo horder hhi hr hrB ha

lemma norm_weighted_sum_le_center (s : Finset ℕ) (c w : ℕ → ℂ) (z : ℂ)
    (E : ℝ) (M : ℕ → ℝ) (hcenter : ‖∑ n ∈ s, c n‖ ≤ E)
    (hc : ∀ n ∈ s, ‖c n‖ ≤ 1) (hw : ∀ n ∈ s, ‖w n - z‖ ≤ M n) :
    ‖∑ n ∈ s, c n * w n‖ ≤ E * ‖z‖ + ∑ n ∈ s, M n := by
  have heq : (∑ n ∈ s, c n * w n) =
      (∑ n ∈ s, c n) * z + ∑ n ∈ s, c n * (w n - z) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, add_sub_cancel]
  have hvariation : ‖∑ n ∈ s, c n * (w n - z)‖ ≤ ∑ n ∈ s, M n := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hc n hn) (hw n hn) (norm_nonneg _) (by norm_num)
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right hcenter (norm_nonneg _)) hvariation

/-- Centering within a cell transfers residue-count cancellation to Mellin weights. -/
theorem norm_rough_subcell_mellin_le {x : ℝ} (hx : 1 < x) (S u : ℝ)
    (n : ℕ) (hn : 0 < n) (s : Finset ℕ) (hs : s ⊆ logCell x S n)
    {r : ℕ} (chi : DirichletCharacter ℂ r) (E : ℝ)
    (hcenter : ‖∑ m ∈ s.filter (rough (W x)), chi (m : ZMod r)‖ ≤ E)
    (hsmall : (1 + |u|) * L x ^ (-S) ≤ 1) :
    ‖∑ m ∈ s.filter (rough (W x)), chi (m : ZMod r) * mellin m u / (m : ℂ)‖ ≤
      E / (n : ℝ) + 2 * (1 + |u|) * L x ^ (-S) * (∑ m ∈ s, (m : ℝ)⁻¹) := by
  have ht : s.filter (rough (W x)) ⊆ logCell x S n :=
    (Finset.filter_subset _ _).trans hs
  have hb := norm_weighted_sum_le_center (s.filter (rough (W x)))
    (fun m => chi (m : ZMod r)) (fun m => mellinWeight m u) (mellinWeight n u) E
    (fun m => 2 * (1 + |u|) * L x ^ (-S) / (m : ℝ)) hcenter
    (fun m _ => chi.norm_le_one _) (fun m hm => mellin_cell_variation hx S u hn (ht hm) hsmall)
  rw [norm_mellinWeight (by exact_mod_cast hn : 0 < (n : ℝ)) u] at hb
  have hmass : (∑ m ∈ s.filter (rough (W x)), (m : ℝ)⁻¹) ≤ ∑ m ∈ s, (m : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun m _ _ => by positivity)
  have hcoeff : 0 ≤ 2 * (1 + |u|) * L x ^ (-S) :=
    mul_nonneg (by positivity) (cell_width_pos hx S).le
  have hb' :
      ‖∑ m ∈ s.filter (rough (W x)), chi (m : ZMod r) * mellin m u / (m : ℂ)‖ ≤
        E / (n : ℝ) + 2 * (1 + |u|) * L x ^ (-S) *
          (∑ m ∈ s.filter (rough (W x)), (m : ℝ)⁻¹) := by
    simpa only [div_eq_mul_inv, Finset.mul_sum, mellinWeight, Complex.ofReal_natCast, mul_assoc]
      using hb
  exact hb'.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass hcoeff))

theorem norm_proxy_subcell_character_mellin_le (I : FactorTest) {x : ℝ} (hx : 1 < x)
    (S u : ℝ) (n : ℕ) (hn : 0 < n) (s : Finset ℕ) (hs : s ⊆ logCell x S n)
    (hden : 0 < proxyDenominator x S n)
    (hsubset : ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m)
    {r : ℕ} (chi : DirichletCharacter ℂ r) (E : ℝ)
    (hcenter : ‖∑ m ∈ s.filter (rough (W x)), chi (m : ZMod r)‖ ≤ E)
    (hsmall : (1 + |u|) * L x ^ (-S) ≤ 1) :
    ‖∑ m ∈ s, (proxy I x S m : ℂ) * chi (m : ZMod r) * mellin m u / (m : ℂ)‖ ≤
      E / (n : ℝ) + 2 * (1 + |u|) * L x ^ (-S) * (∑ m ∈ s, (m : ℝ)⁻¹) := by
  have heq : (∑ m ∈ s, (proxy I x S m : ℂ) * chi (m : ZMod r) *
      mellin m u / (m : ℂ)) = (proxyConstant I x S n : ℂ) *
      (∑ m ∈ s.filter (rough (W x)), chi (m : ZMod r) * mellin m u / (m : ℂ)) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hr : rough (W x) m
    · simp only [proxy, hr, ite_true,
        proxyConstant_eq_of_mem I hx S (hs hm), mul_assoc, mul_div_assoc]
    · simp only [proxy, hr, ite_false, Complex.ofReal_zero, zero_mul, zero_div]
  have hc : ‖(proxyConstant I x S n : ℂ)‖ ≤ 1 := by
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (proxyConstant_nonneg I x S n)]
    exact proxyConstant_le_one I x S n hden hsubset
  rw [heq, norm_mul]
  apply (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans
  simpa only [one_mul] using norm_rough_subcell_mellin_le hx S u n hn s hs chi E hcenter hsmall

end Erdos821.P8Core

