import Erdos821.P8.SharpDenominator

noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma primesUpTo_mono {Y Z : ℝ} (hYZ : Y ≤ Z) : primesUpTo Y ⊆ primesUpTo Z := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hYZ)⟩, hp.2⟩

lemma prime_Ioc_eq_sdiff (Y Z : ℝ) :
    (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime = primesUpTo Z \ primesUpTo Y := by
  ext p
  by_cases hp : p.Prime
  · have hp1 := hp.one_lt
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc,
      Finset.mem_Ioc, hp, and_true]
    omega
  · simp [primesUpTo, hp]

lemma prime_Ioc_card (Y Z : ℝ) (hYZ : Y ≤ Z) :
    (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) =
      ((primesUpTo Z).card : ℝ) - ((primesUpTo Y).card : ℝ) := by
  have hcard := Finset.card_sdiff_add_card_eq_card (primesUpTo_mono hYZ)
  rw [← prime_Ioc_eq_sdiff] at hcard
  have hcast : (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter Nat.Prime).card : ℝ) +
      ((primesUpTo Y).card : ℝ) = ((primesUpTo Z).card : ℝ) := by exact_mod_cast hcard
  linarith

lemma inv_log_intervalIntegrable {Y Z : ℝ} (hY : 2 ≤ Y) (hYZ : Y ≤ Z) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume Y Z := by
  have hcont : ContinuousOn Real.log (Set.Icc Y Z) :=
    Real.continuousOn_log.mono (fun t ht => (by linarith [ht.1] : t ≠ 0))
  exact (hcont.inv₀ (fun t ht => (Real.log_pos (by linarith [ht.1])).ne')).intervalIntegrable_of_Icc hYZ

lemma li_sub_le {Y Z : ℝ} (hY : 2 ≤ Y) (hYZ : Y ≤ Z) :
    li Z - li Y ≤ (Z - Y) / Real.log Y := by
  have hintYZ := inv_log_intervalIntegrable hY hYZ
  have hint2Y := inv_log_intervalIntegrable (by norm_num : (2 : ℝ) ≤ 2) hY
  have hint2Z := inv_log_intervalIntegrable (by norm_num : (2 : ℝ) ≤ 2) (hY.trans hYZ)
  rw [li, li, intervalIntegral.integral_interval_sub_left hint2Z hint2Y]
  calc
    (∫ t : ℝ in Y..Z, (Real.log t)⁻¹) ≤ ∫ _t : ℝ in Y..Z, (Real.log Y)⁻¹ := by
      apply intervalIntegral.integral_mono_on hYZ hintYZ (intervalIntegrable_const)
      intro t ht
      exact inv_anti₀ (Real.log_pos (by linarith))
        (Real.log_le_log (by linarith : 0 < Y) ht.1)
    _ = (Z - Y) / Real.log Y := by
      rw [intervalIntegral.integral_const]
      simp [div_eq_mul_inv]

lemma logCell_length_upper {x : ℝ} (hx : 1 < x) (S : ℝ) (n : ℕ)
    (hdelta : L x ^ (-S) ≤ 1) :
    logCellUpper x S n - logCellLower x S n ≤ 2 * L x ^ (-S) * logCellLower x S n := by
  have hdelta0 := cell_width_pos hx S
  have hexp := Real.abs_exp_sub_one_le (show |L x ^ (-S)| ≤ 1 by rwa [abs_of_pos hdelta0])
  rw [abs_of_pos hdelta0] at hexp
  have hexp' : Real.exp (L x ^ (-S)) - 1 ≤ 2 * L x ^ (-S) := (le_abs_self _).trans hexp
  have hY : 0 ≤ logCellLower x S n := by unfold logCellLower; positivity
  have hmul := mul_le_mul_of_nonneg_left hexp' hY
  rw [logCell_endpoint_relation]
  nlinarith

/-- Ordinary PNT endpoint errors give an absolute cell bound independent of the mesh exponent. -/
theorem eventually_prime_logCell_upper (hc : ClassicalInputs) (S : ℝ) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      x ^ ((1 : ℝ) / 4) ≤ (n : ℝ) → (n : ℝ) ≤ x ^ ((3 : ℝ) / 4) →
      (((logCell x S n).filter Nat.Prime).card : ℝ) ≤
        17 * L x ^ (-S) * logCellLower x S n / L x := by
  obtain ⟨K, hK, hprog⟩ := hc.progressions (S + 2) 1 (by linarith) (by norm_num)
  obtain ⟨y0, hy0⟩ := eventually_atTop.mp hprog
  let c : ℝ := (1 / 8 : ℝ) ^ (-(S + 2))
  let E : ℝ := 4 * K * c
  have hsmall : ∀ᶠ x : ℝ in atTop, E * L x ^ (-1 : ℝ) ≤ 1 :=
    ((((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
      Real.tendsto_log_atTop).const_mul E).eventually
      (eventually_lt_nhds (by simp : E * (0 : ℝ) < 1))).mono (fun _ h => h.le)
  have hL : ∀ᶠ x : ℝ in atTop, 8 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  have hlarge : ∀ᶠ x : ℝ in atTop, max 2 y0 ≤ x ^ ((1 : ℝ) / 8) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually (eventually_ge_atTop _)
  have hcells := eventually_logCell_endpoint_bounds 1 S (by norm_num) hS
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL, hlarge, hsmall, hcells]
    with x hx hLx hlargeX hsmallX hcellsX
  intro n hnlo hnhi
  rcases hcellsX n hnlo (by convert hnhi using 1; norm_num) with ⟨hY, hYZ, _hZ⟩
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L x := by linarith
  have hY2 : 2 ≤ logCellLower x S n := (le_max_left _ _).trans (hlargeX.trans hY)
  have hYthreshold : y0 ≤ logCellLower x S n := (le_max_right _ _).trans (hlargeX.trans hY)
  have hY0 : 0 < logCellLower x S n := by linarith
  have hZ0 : 0 < logCellUpper x S n := hY0.trans_le hYZ
  have hlogY : L x / 8 ≤ Real.log (logCellLower x S n) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 8)) hY
    rw [Real.log_rpow hx0] at h
    dsimp only [L]
    linarith
  have hlogZ : L x / 8 ≤ Real.log (logCellUpper x S n) :=
    hlogY.trans (Real.log_le_log hY0 hYZ)
  have hlogY1 : 1 ≤ Real.log (logCellLower x S n) := by linarith
  have hlogZ1 : 1 ≤ Real.log (logCellUpper x S n) := by linarith
  have hdelta : L x ^ (-S) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hlength := logCell_length_upper hx S n hdelta
  have hZthree : logCellUpper x S n ≤ 3 * logCellLower x S n := by
    have := mul_le_mul_of_nonneg_right hdelta hY0.le
    nlinarith
  have hpower : ∀ t : ℝ, L x / 8 ≤ Real.log t →
      Real.log t ^ (-(S + 2)) ≤ L x ^ (-(S + 2)) * c := by
    intro t ht
    calc
      Real.log t ^ (-(S + 2)) ≤ (L x / 8) ^ (-(S + 2)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) ht (by linarith)
      _ = L x ^ (-(S + 2)) * c := by
        rw [show L x / 8 = L x * (1 / 8) by ring, Real.mul_rpow hL0.le (by norm_num)]
  have hcountY := hy0 (logCellLower x S n) hYthreshold 1 0 (by norm_num)
    (by simpa only [Nat.cast_one, Real.rpow_one] using hlogY1) (by simp)
  have hcountZ := hy0 (logCellUpper x S n) (hYthreshold.trans hYZ) 1 0 (by norm_num)
    (by simpa only [Nat.cast_one, Real.rpow_one] using hlogZ1) (by simp)
  simp only [Nat.mod_one, Nat.totient_one, Nat.cast_one, div_one, eq_self,
    Finset.filter_true] at hcountY hcountZ
  have herror : K * logCellLower x S n * Real.log (logCellLower x S n) ^ (-(S + 2)) +
      K * logCellUpper x S n * Real.log (logCellUpper x S n) ^ (-(S + 2)) ≤
        E * logCellLower x S n * L x ^ (-(S + 2)) := by
    calc
      _ ≤ K * logCellLower x S n * (L x ^ (-(S + 2)) * c) +
          K * logCellUpper x S n * (L x ^ (-(S + 2)) * c) := by
        gcongr
        · exact hpower _ hlogY
        · exact hpower _ hlogZ
      _ ≤ K * logCellLower x S n * (L x ^ (-(S + 2)) * c) +
          K * (3 * logCellLower x S n) * (L x ^ (-(S + 2)) * c) := by
        gcongr
      _ = E * logCellLower x S n * L x ^ (-(S + 2)) := by dsimp [E]; ring
  have hfactor : L x ^ (-(S + 2)) = L x ^ (-S) / L x * L x ^ (-1 : ℝ) := by
    rw [← Real.rpow_sub_one hL0.ne', ← Real.rpow_add hL0]
    congr 1
    ring
  have herrorSmall : E * logCellLower x S n * L x ^ (-(S + 2)) ≤
      L x ^ (-S) * logCellLower x S n / L x := by
    calc
      _ = (L x ^ (-S) * logCellLower x S n / L x) * (E * L x ^ (-1 : ℝ)) := by
        rw [hfactor]
        ring
      _ ≤ (L x ^ (-S) * logCellLower x S n / L x) * 1 := by gcongr
      _ = _ := mul_one _
  have hli : li (logCellUpper x S n) - li (logCellLower x S n) ≤
      16 * L x ^ (-S) * logCellLower x S n / L x := by
    calc
      _ ≤ (logCellUpper x S n - logCellLower x S n) / Real.log (logCellLower x S n) :=
        li_sub_le hY2 hYZ
      _ ≤ (2 * L x ^ (-S) * logCellLower x S n) / (L x / 8) := by
        exact div_le_div₀ (by positivity) hlength (by positivity) hlogY
      _ = _ := by field_simp; ring
  rw [logCell_eq_endpoints, prime_Ioc_card _ _ hYZ]
  rw [show 17 * L x ^ (-S) * logCellLower x S n / L x =
    16 * L x ^ (-S) * logCellLower x S n / L x +
      L x ^ (-S) * logCellLower x S n / L x by ring]
  have hupper := (abs_le.mp hcountZ).2
  have hlower := (abs_le.mp hcountY).1
  linarith [herror.trans herrorSmall]

/-- The prime part of ProxyDensities, with one constant for every allowed kappa and S. -/
theorem prime_proxy_density_from_residue (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) :
    ∃ K : ℝ, 0 < K ∧ ∀ kappa S : ℝ, 0 < kappa → kappa < 1 / 50 → 0 < S →
      ∀ᶠ x : ℝ in atTop, ∀ m : ℕ,
        x ^ (1 / 2 - 2 * kappa) ≤ (m : ℝ) → (m : ℝ) ≤ x ^ (1 / 2 + 2 * kappa) →
        proxyConstant .prime x S m ≤ K / (L x * sieveProduct (W x)) := by
  refine ⟨34, by norm_num, ?_⟩
  intro kappa S hkappa hkappaMax hS
  have hden := eventually_proxyDenominator_sharp_lower hc hs hresidue 1 S (1 / 2)
    (by norm_num) hS (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hden,
    eventually_prime_logCell_upper hc S hS] with x hx hdenX hprime
  intro m hmlo hmhi
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L x := Real.log_pos hx
  have hmlo' : x ^ ((1 : ℝ) / 4) ≤ (m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)).trans hmlo
  have hmhi' : (m : ℝ) ≤ x ^ ((3 : ℝ) / 4) :=
    hmhi.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  have hdenM := hdenX m hmlo' (by convert hmhi' using 1; norm_num)
  norm_num at hdenM
  have hprimeM := hprime m hmlo' hmhi'
  have hV0 := sieveProduct_pos (W x)
  have hY0 : 0 < logCellLower x S m := by unfold logCellLower; positivity
  have hdelta0 := cell_width_pos hx S
  have hD0 : 0 < (proxyDenominator x S m : ℝ) :=
    lt_of_lt_of_le (by positivity) hdenM
  have hnum : (∑ p ∈ logCell x S m, test .prime x p) =
      (((logCell x S m).filter Nat.Prime).card : ℝ) := by
    simp [test, Finset.sum_boole]
  rw [proxyConstant, hnum]
  apply (div_le_div_iff₀ hD0 (by positivity : 0 < L x * sieveProduct (W x))).mpr
  have hscaled := mul_le_mul_of_nonneg_right hprimeM (by positivity : 0 ≤ L x * sieveProduct (W x))
  have hcancel : (17 * L x ^ (-S) * logCellLower x S m / L x) *
      (L x * sieveProduct (W x)) = 17 * L x ^ (-S) * logCellLower x S m *
        sieveProduct (W x) := by field_simp
  rw [hcancel] at hscaled
  nlinarith

end Erdos821.P8Core

