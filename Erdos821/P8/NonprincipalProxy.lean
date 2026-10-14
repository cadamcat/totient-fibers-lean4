import Erdos821.P8.CellCounting

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma sieveProduct_le_one (y : ℝ) : sieveProduct y ≤ 1 := by
  change (∏ p ∈ primesUpTo y, (1 - (p : ℝ)⁻¹)) ≤ 1
  calc
    _ ≤ ∏ _p ∈ primesUpTo y, (1 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hp2 := (mem_primesUpTo.mp hp).1.two_le
        have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
        have hinv : (p : ℝ)⁻¹ ≤ 1 := by
          simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hp1
        linarith
      · intro p _
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p))
    _ = 1 := by simp

lemma subcell_span_div_le {x : ℝ} (hx : 1 < x) (S : ℝ) (hle : L x ^ (-S) ≤ 1)
    {n m k : ℕ} (hn : 0 < n) (hm : 0 < m) (hmk : m ≤ k)
    (hsubset : Finset.Icc m k ⊆ logCell x S n) :
    ((k : ℝ) - ((m : ℝ) - 1)) / (n : ℝ) ≤ Real.exp 1 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hm.trans_le hmk
  have hmem := hsubset (Finset.right_mem_Icc.mpr hmk)
  have hlog := (abs_le.mp (abs_log_sub_le_width hx S hn hmem)).2
  have hkexp : (k : ℝ) ≤ Real.exp 1 * (n : ℝ) := by
    have hln : Real.log k ≤ Real.log n + 1 := by linarith
    have he := Real.exp_le_exp.mpr hln
    simpa only [Real.exp_add, Real.exp_log hk0, Real.exp_log hn0, mul_comm] using he
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  apply (div_le_iff₀ hn0).mpr
  linarith

lemma residue_error_div_le {x : ℝ} (hx : 1 < x) (b B A : ℝ) {r n : ℕ}
    (hr : 1 ≤ r) (hrB : (r : ℝ) ≤ L x ^ B) (hn : x ^ (b / 4) ≤ (n : ℝ))
    (span : ℝ) (hspan : 0 ≤ span) (hspanDiv : span / (n : ℝ) ≤ Real.exp 1) :
    ((r : ℝ) * (span * sieveProduct (W x) / (Nat.totient r : ℝ) * L x ^ (-A) +
      x ^ (b / 16))) / (n : ℝ) ≤
      L x ^ B * (Real.exp 1 * L x ^ (-A) + x ^ (-3 * b / 16)) := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L x := Real.log_pos hx
  have hxpow : 0 < x ^ (b / 4) := Real.rpow_pos_of_pos hx0 _
  have hn0 : 0 < (n : ℝ) := hxpow.trans_le hn
  have hphi : (1 : ℝ) ≤ Nat.totient r := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < r))
  have hV0 : 0 ≤ sieveProduct (W x) := (sieveProduct_pos _).le
  have hmain : span * sieveProduct (W x) / (Nat.totient r : ℝ) ≤ span := by
    calc
      _ ≤ span * sieveProduct (W x) := div_le_self (mul_nonneg hspan hV0) hphi
      _ ≤ span := by simpa using mul_le_mul_of_nonneg_left (sieveProduct_le_one _) hspan
  have hmainDiv : (span * sieveProduct (W x) / (Nat.totient r : ℝ)) / (n : ℝ) ≤
      Real.exp 1 := (div_le_div_of_nonneg_right hmain hn0.le).trans hspanDiv
  have habs : x ^ (b / 16) / (n : ℝ) ≤ x ^ (-3 * b / 16) := by
    have h := div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le (b / 16)) hxpow hn
    have heq : x ^ (b / 16) / x ^ (b / 4) = x ^ (-3 * b / 16) := by
      rw [← Real.rpow_sub hx0]
      congr 1
      ring
    exact h.trans_eq heq
  have hpow0 : 0 ≤ L x ^ (-A) := Real.rpow_nonneg hL0.le _
  calc
    _ = (r : ℝ) * ((span * sieveProduct (W x) / (Nat.totient r : ℝ)) / (n : ℝ) *
        L x ^ (-A) + x ^ (b / 16) / (n : ℝ)) := by ring
    _ ≤ (r : ℝ) * (Real.exp 1 * L x ^ (-A) + x ^ (-3 * b / 16)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
      exact add_le_add (mul_le_mul_of_nonneg_right hmainDiv hpow0) habs
    _ ≤ L x ^ B * (Real.exp 1 * L x ^ (-A) + x ^ (-3 * b / 16)) :=
      mul_le_mul_of_nonneg_right hrB (by positivity)

theorem eventually_proxy_subcell_bound (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b kappa B S A : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hA : 0 < A) (hBS : B < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (n m k r : ℕ)
      (chi : DirichletCharacter ℂ r) (u : ℝ),
      TestAllowed b kappa I → x ^ (b / 4) ≤ (n : ℝ) → (n : ℝ) ≤ x ^ (1 - b / 4) →
      x ^ (b / 4) ≤ (m : ℝ) → m ≤ k → (k : ℝ) ≤ x ^ (2 : ℕ) →
      Finset.Icc m k ⊆ logCell x S n →
      1 ≤ r → (r : ℝ) ≤ L x ^ B → chi ≠ 1 → |u| ≤ L x ^ B →
      ‖∑ v ∈ Finset.Icc m k, (proxy I x S v : ℂ) * chi (v : ZMod r) *
        mellin v u / (v : ℂ)‖ ≤
        L x ^ B * (Real.exp 1 * L x ^ (-A) + x ^ (-3 * b / 16)) +
        2 * (1 + |u|) * L x ^ (-S) * (∑ v ∈ Finset.Icc m k, (v : ℝ)⁻¹) := by
  have hS : 0 < S := hB.trans hBS
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL,
    eventually_integer_lower_endpoint b hb,
    eventually_proxyDenominator_pos hc hs hresidue b S hb hS,
    eventually_test_supported_on_cells b kappa S hb hS,
    eventually_mellin_small_argument B S hB hBS,
    eventually_rough_character_interval_bound hc hs hresidue (b / 8) 2 B A (b / 16)
      (by linarith) (by norm_num) hB hA (by linarith)] with x hx hLx hstart hden hsupport harg hcount
  intro I n m k r chi u hallowed hnlo hnhi hmlo hmk hkhi hcell hr hrB hchi hu
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < n := by exact_mod_cast (Real.rpow_pos_of_pos hx0 (b / 4)).trans_le hnlo
  have hm0 : 0 < m := by exact_mod_cast (Real.rpow_pos_of_pos hx0 (b / 4)).trans_le hmlo
  have hwidth : L x ^ (-S) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hLx (by linarith)
  have hspan : 0 ≤ (k : ℝ) - ((m : ℝ) - 1) := by
    have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
    linarith
  have hcount' := hcount ((m : ℝ) - 1) (k : ℝ) r chi (hstart m hmlo)
    (by linarith) (by simpa only [Real.rpow_two] using hkhi) hr hrB hchi
  rw [← Icc_eq_real_Ioc hm0] at hcount'
  have hweighted := norm_proxy_subcell_character_mellin_le I hx S u n hn0 (Finset.Icc m k)
    hcell (hden n hnlo hnhi) (hsupport I n hallowed hnlo) chi _ hcount' (harg u hu)
  have herror := residue_error_div_le hx b B A hr hrB hnlo _ hspan
    (subcell_span_div_le hx S hwidth hn0 hm0 hmk hcell)
  exact hweighted.trans (add_le_add herror le_rfl)

theorem eventually_proxy_interval_estimate (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b kappa B S A : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hA : 0 < A) (hBS : B < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (a z r : ℕ)
      (chi : DirichletCharacter ℂ r) (u : ℝ),
      TestAllowed b kappa I → x ^ (b / 4) ≤ (a : ℝ) → a ≤ z →
      (z : ℝ) ≤ x ^ (1 - b / 4) → 1 ≤ r → (r : ℝ) ≤ L x ^ B → chi ≠ 1 → |u| ≤ L x ^ B →
      ‖∑ v ∈ Finset.Icc a z, (proxy I x S v : ℂ) * chi (v : ZMod r) *
        mellin v u / (v : ℂ)‖ ≤
        4 * L x ^ (S + 1) * L x ^ B * (Real.exp 1 * L x ^ (-A) + x ^ (-3 * b / 16)) +
        2 * (1 + |u|) * L x ^ (-S) * (∑ v ∈ Finset.Icc a z, (v : ℝ)⁻¹) := by
  have hS : 0 < S := hB.trans hBS
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL,
    eventually_proxy_subcell_bound hc hs hresidue b kappa B S A hb hB hA hBS]
    with x hx hLx hcells
  intro I a z r chi u hallowed halo haz hzhi hr hrB hchi hu
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L x := zero_lt_one.trans_le hLx
  have ha : 0 < a := by exact_mod_cast (Real.rpow_pos_of_pos hx0 (b / 4)).trans_le halo
  have hzprobe : (z : ℝ) ≤ x ^ (2 : ℕ) := by
    apply hzhi.trans
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : 1 - b / 4 ≤ 2)
  let t := (Finset.Icc a z).image (logIndex (L x ^ (-S)))
  let fiber := fun j => (Finset.Icc a z).filter (fun v => logIndex (L x ^ (-S)) v = j)
  let C := L x ^ B * (Real.exp 1 * L x ^ (-A) + x ^ (-3 * b / 16))
  let M := 2 * (1 + |u|) * L x ^ (-S)
  let f := fun v => (proxy I x S v : ℂ) * chi (v : ZMod r) * mellin v u / (v : ℂ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ j ∈ t, ‖∑ v ∈ fiber j, f v‖ ≤ C + M * (∑ v ∈ fiber j, (v : ℝ)⁻¹) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨n, hn, hnj⟩
    rcases Finset.mem_Icc.mp hn with ⟨han, hnz⟩
    let m := max a (⌊Real.exp ((j : ℝ) * L x ^ (-S))⌋₊ + 1)
    let k := min z ⌊Real.exp (((j : ℝ) + 1) * L x ^ (-S))⌋₊
    have hf : fiber j = Finset.Icc m k := interval_logIndex_fiber_shape (cell_width_pos hx S) ha j
    have hnf : n ∈ fiber j := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨han, hnz⟩, hnj⟩
    have hmk : m ≤ k := by rw [hf] at hnf; exact (Finset.mem_Icc.mp hnf).1.trans (Finset.mem_Icc.mp hnf).2
    have hcell : Finset.Icc m k ⊆ logCell x S n := by
      rw [← hf, logCell_eq_index, hnj]
      exact interval_logIndex_fiber_subset (cell_width_pos hx S) ha j
    have hnlo : x ^ (b / 4) ≤ (n : ℝ) := halo.trans (by exact_mod_cast han)
    have hnhi : (n : ℝ) ≤ x ^ (1 - b / 4) := (by exact_mod_cast hnz : (n : ℝ) ≤ z).trans hzhi
    have hmlo : x ^ (b / 4) ≤ (m : ℝ) := halo.trans (by exact_mod_cast (le_max_left a _))
    have hkprobe : (k : ℝ) ≤ x ^ (2 : ℕ) :=
      (by exact_mod_cast (min_le_left z _) : (k : ℝ) ≤ z).trans hzprobe
    have h := hcells I n m k r chi u hallowed hnlo hnhi hmlo hmk hkprobe hcell hr hrB hchi hu
    simpa only [hf, C, M, f] using h
  have hcount : (t.card : ℝ) ≤ 4 * L x ^ (S + 1) := interval_logCell_count_le hx hLx S hS ha hzprobe
  calc
    ‖∑ v ∈ Finset.Icc a z, f v‖ = ‖∑ j ∈ t, ∑ v ∈ fiber j, f v‖ := by
      rw [interval_sum_by_logIndex]
    _ ≤ ∑ j ∈ t, ‖∑ v ∈ fiber j, f v‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ t, (C + M * (∑ v ∈ fiber j, (v : ℝ)⁻¹)) := Finset.sum_le_sum hbound
    _ = (t.card : ℝ) * C + M * (∑ v ∈ Finset.Icc a z, (v : ℝ)⁻¹) := by
      rw [Finset.sum_add_distrib]
      have hconst : (∑ _j ∈ t, C) = (t.card : ℝ) * C := by simp only [Finset.sum_const, nsmul_eq_mul]
      have hmass : (∑ j ∈ t, M * (∑ v ∈ fiber j, (v : ℝ)⁻¹)) =
          M * (∑ v ∈ Finset.Icc a z, (v : ℝ)⁻¹) := by
        rw [← Finset.mul_sum, interval_sum_by_logIndex]
      rw [hconst, hmass]
    _ ≤ 4 * L x ^ (S + 1) * C + M * (∑ v ∈ Finset.Icc a z, (v : ℝ)⁻¹) :=
      add_le_add (mul_le_mul_of_nonneg_right hcount hC) le_rfl
    _ = _ := by dsimp [C, M]; ring

end Erdos821.P8Core

