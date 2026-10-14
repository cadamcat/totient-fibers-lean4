import Erdos821.P6Off.PreCauchyPairs

noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem pairSum_sub (U V : ℝ) (F H alpha beta : ℕ → ℂ) :
    pairSum U V F alpha beta-pairSum U V H alpha beta =
      pairSum U V (fun u => F u-H u) alpha beta := by
  unfold pairSum
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> ring

theorem pairSum_weighted_stability (D : BandData) (x : ℝ) (jstar : ℕ) (U V eps M : ℝ)
    (F H alpha beta : ℕ → ℂ) (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (hFH : ∀ u, 0 < u → ‖F u-H u‖ ≤ eps*D.weight x jstar u)
    (ha : ∀ m, ‖alpha m‖ ≤ M) (hb : ∀ n, ‖beta n‖ ≤ M) :
    ‖pairSum U V F alpha beta-pairSum U V H alpha beta‖ ≤
      eps*M^2*weightedPairMass D x jstar U V := by
  rw [pairSum_sub]
  unfold pairSum
  calc
    _ ≤ ∑ m ∈ dyad U, ∑ n ∈ dyad V,
      ‖if Odd (m*n) ∧ 1 < m*n then (F ((m*n-1)/2)-H ((m*n-1)/2))*alpha m*beta n else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ m ∈ dyad U, ∑ n ∈ dyad V,
      eps*M^2*(if Odd (m*n) ∧ 1 < m*n then D.weight x jstar ((m*n-1)/2) else 0) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      split_ifs with h
      · have hw := band_weight_nonneg D x jstar ((m*n-1)/2)
        have h1 := mul_le_mul (hFH _ (odd_shift_identity _ h.1 h.2).1) (ha m)
          (norm_nonneg _) (mul_nonneg heps hw)
        have h2 := mul_le_mul h1 (hb n) (norm_nonneg _) (mul_nonneg (mul_nonneg heps hw) hM)
        simpa only [norm_mul, pow_two, mul_assoc, mul_comm, mul_left_comm] using h2
      · simp
    _ = _ := by simp only [weightedPairMass, Finset.mul_sum]

theorem cutoff_norm_le_mass (psi : ℝ → ℝ) (f : ℝ → ℂ) (hf : Integrable f)
    (hrep : ∀ z, (psi (Real.exp z) : ℂ) = ∫ t, f t*e (t*z))
    (y : ℝ) (hy : 0 < y) : ‖(psi y : ℂ)‖ ≤ ∫ t, ‖f t‖ := by
  rw [← Real.exp_log hy, hrep]
  apply le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with t
  simp only [norm_mul, Erdos821.S56Core.norm_e, mul_one]

theorem cutoff_truncation_polylog (psi : ℝ → ℝ) (f : ℝ → ℂ) (hf : Integrable f)
    (hm : ∀ k, Integrable (fun t => ‖t‖^k*‖f t‖))
    (hrep : ∀ z, (psi (Real.exp z) : ℂ) = ∫ t, f t*e (t*z)) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, 0 < u →
      ‖(psi ((u:ℝ)/x) : ℂ)-truncatedCutoff f (L x) x u‖ ≤ K*L x^(-A) := by
  obtain ⟨k, hk⟩ := exists_nat_gt A
  let K := (∫ t, ‖t‖^k*‖f t‖)+1
  have hK : 0 < K := by
    have hi : 0 ≤ ∫ t, ‖t‖^k*‖f t‖ := integral_nonneg (fun _ => by positivity)
    change 0 < (∫ t, ‖t‖^k*‖f t‖)+1
    exact add_pos_of_nonneg_of_pos hi zero_lt_one
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_gt_atTop 0, tendsto_L.eventually (eventually_ge_atTop 1)] with x hx hL
  intro u hu
  have hup : (0:ℝ) < u := by exact_mod_cast hu
  have hid : Real.exp (Real.log (u:ℝ)-Real.log x) = (u:ℝ)/x := by
    rw [Real.exp_sub, Real.exp_log hup, Real.exp_log hx]
  have hraw := fixed_fourier_truncation (fun z => (psi (Real.exp z) : ℂ)) f hf hrep k
    (hm k) (L x) (zero_lt_one.trans_le hL) (Real.log (u:ℝ)-Real.log x)
  rw [hid] at hraw
  change ‖(psi ((u:ℝ)/x) : ℂ)-truncatedCutoff f (L x) x u‖ ≤ _ at hraw
  have hKbound : (∫ t, ‖t‖^k*‖f t‖) ≤ K := by dsimp [K]; linarith
  have hpower : (L x^k)⁻¹ ≤ L x^(-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (zero_le_one.trans hL)]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  exact hraw.trans (by
    have h := mul_le_mul hpower hKbound (integral_nonneg (fun _ => by positivity))
      (Real.rpow_nonneg (zero_le_one.trans hL) (-A))
    simpa only [mul_comm] using h)

theorem discarded_rough_pair_mass_bound (D : BandData) (x : ℝ) (jstar : ℕ)
    (U V sigma : ℝ) (hx : 5 ≤ x) :
    (∑ m ∈ dyad U, ∑ n ∈ dyad V,
      if Odd (m*n) ∧ 1 < m*n ∧ rough (W x) m ∧ (m*n-1)/2 ≤ ⌊2*x⌋₊ then
        (if x^sigma < (groupPart (D.groups x) ((m*n-1)/2) : ℝ) then D.weight x jstar ((m*n-1)/2) else 0)
      else 0) ≤
      Real.exp (2*Real.sqrt (L x)) * ∑ u ∈ Finset.Icc 1 ⌊2*x⌋₊,
        if x^sigma < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0 := by
  let H := fun u => if x^sigma < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0
  have hH : ∀ u, 0 ≤ H u := by
    intro u
    dsimp [H]
    split_ifs
    · exact band_weight_nonneg D x jstar u
    · exact le_rfl
  apply (sum_shifted_rough_pairs_le (dyad U) (dyad V) ⌊2*x⌋₊ (W x) H hH).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hulo := (Finset.mem_Icc.mp hu).1
  have huhi := (Finset.mem_Icc.mp hu).2
  have hux : (u:ℝ) ≤ 2*x := (by exact_mod_cast huhi : (u:ℝ) ≤ ⌊2*x⌋₊).trans (Nat.floor_le (by linarith))
  have hsize : ((2*u+1:ℕ):ℝ) ≤ 5*x := by push_cast; linarith
  exact mul_le_mul_of_nonneg_right (rough_divisor_exp_bound x hx (2*u+1) (by omega) hsize) (hH u)

theorem pairSum_allocation_tail_bound (D : BandData) (x : ℝ) (jstar : ℕ)
    (emin E U V sigma M Mf : ℝ) (psi : ℝ → ℝ) (alpha beta : ℕ → ℂ)
    (hx : 5 ≤ x) (hM : 0 ≤ M) (hMf : 0 ≤ Mf)
    (hsupp : Function.support psi ⊆ Set.Icc 1 2)
    (hpsi : ∀ y, 0 < y → ‖(psi y : ℂ)‖ ≤ Mf)
    (hgood : ∀ u : ℕ, x ≤ (u:ℝ) → (groupPart (D.groups x) u : ℝ) ≤ x^sigma →
      allocatedWeight D x jstar emin E u = D.weight x jstar u)
    (ha : ∀ m, ‖alpha m‖ ≤ M) (hb : ∀ n, ‖beta n‖ ≤ M)
    (hrough : ∀ m, alpha m ≠ 0 → rough (W x) m) :
    ‖pairSum U V (fun u => (D.weight x jstar u*psi ((u:ℝ)/x) : ℝ)) alpha beta-
      pairSum U V (fun u => (allocatedWeight D x jstar emin E u*psi ((u:ℝ)/x) : ℝ)) alpha beta‖ ≤
    Mf*M^2*Real.exp (2*Real.sqrt (L x))*∑ u ∈ Finset.Icc 1 ⌊2*x⌋₊,
      if x^sigma < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0 := by
  have hxpos : 0 < x := by linarith
  have hpoint (u : ℕ) (hu : 0 < u) :
      ‖(D.weight x jstar u*psi ((u:ℝ)/x) : ℝ)-
        (allocatedWeight D x jstar emin E u*psi ((u:ℝ)/x) : ℝ)‖ ≤
      Mf*(if u ≤ ⌊2*x⌋₊ then
        (if x^sigma < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0) else 0) := by
    by_cases hpsiz : psi ((u:ℝ)/x) = 0
    · simp only [hpsiz, mul_zero, sub_self, norm_zero]
      have hw0 := band_weight_nonneg D x jstar u
      split_ifs <;> positivity
    · have hs := hsupp hpsiz
      have hux : x ≤ (u:ℝ) := by
        have h := (le_div_iff₀ hxpos).mp hs.1
        simpa using h
      have huN : u ≤ ⌊2*x⌋₊ := Nat.le_floor ((div_le_iff₀ hxpos).mp hs.2)
      rw [if_pos huN]
      by_cases hbad : x^sigma < (groupPart (D.groups x) u : ℝ)
      · rw [if_pos hbad]
        obtain ⟨haw0, haw⟩ := allocatedWeight_bounds D x jstar emin E u
        have hdiff0 : 0 ≤ D.weight x jstar u-allocatedWeight D x jstar emin E u := sub_nonneg.mpr haw
        have hdiff : D.weight x jstar u-allocatedWeight D x jstar emin E u ≤ D.weight x jstar u := by linarith
        rw [← sub_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hdiff0]
        have hup : (0:ℝ) < u := by exact_mod_cast hu
        have hp := hpsi ((u:ℝ)/x) (div_pos hup hxpos)
        have hmul := mul_le_mul hdiff hp (norm_nonneg _) (band_weight_nonneg D x jstar u)
        simpa only [Complex.norm_real, mul_comm] using hmul
      · rw [if_neg hbad, hgood u hux (le_of_not_gt hbad)]
        simp
  rw [pairSum_sub]
  unfold pairSum
  let B := fun u => if x^sigma < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0
  have hB : ∀ u, 0 ≤ B u := by
    intro u
    dsimp [B]
    split_ifs
    · exact band_weight_nonneg D x jstar u
    · exact le_rfl
  calc
    _ ≤ ∑ m ∈ dyad U, ∑ n ∈ dyad V,
      ‖if Odd (m*n) ∧ 1 < m*n then
        ((D.weight x jstar ((m*n-1)/2)*psi (((m*n-1)/2:ℕ)/x) : ℝ)-
          (allocatedWeight D x jstar emin E ((m*n-1)/2)*psi (((m*n-1)/2:ℕ)/x) : ℝ))*alpha m*beta n else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ m ∈ dyad U, ∑ n ∈ dyad V,
      Mf*M^2*(if Odd (m*n) ∧ 1 < m*n ∧ rough (W x) m ∧ (m*n-1)/2 ≤ ⌊2*x⌋₊ then B ((m*n-1)/2) else 0) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      by_cases hgate : Odd (m*n) ∧ 1 < m*n
      · rw [if_pos hgate]
        by_cases ham : alpha m = 0
        · have hB0 := hB ((m*n-1)/2)
          simp only [ham, mul_zero, zero_mul, norm_zero]
          split_ifs <;> positivity
        · have hr := hrough m ham
          have hp := hpoint ((m*n-1)/2) (odd_shift_identity _ hgate.1 hgate.2).1
          by_cases huN : (m*n-1)/2 ≤ ⌊2*x⌋₊
          · rw [if_pos huN] at hp
            have hc : Odd (m*n) ∧ 1 < m*n ∧ rough (W x) m ∧ (m*n-1)/2 ≤ ⌊2*x⌋₊ :=
              ⟨hgate.1, hgate.2, hr, huN⟩
            rw [if_pos hc, norm_mul, norm_mul]
            have h1 := mul_le_mul hp (ha m) (norm_nonneg _) (mul_nonneg hMf (hB _))
            have h2 := mul_le_mul h1 (hb n) (norm_nonneg _) (mul_nonneg (mul_nonneg hMf (hB _)) hM)
            simpa only [B, pow_two, mul_assoc, mul_comm, mul_left_comm,
              ← Complex.ofReal_sub, Complex.norm_real] using h2
          · rw [if_neg huN, mul_zero] at hp
            have hc : ¬(Odd (m*n) ∧ 1 < m*n ∧ rough (W x) m ∧ (m*n-1)/2 ≤ ⌊2*x⌋₊) := fun h => huN h.2.2.2
            rw [if_neg hc]
            simp only [mul_zero]
            rw [norm_mul, norm_mul]
            have hnzero := le_antisymm hp (norm_nonneg _)
            simp only [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, hnzero, zero_mul, le_refl]
      · have hc : ¬(Odd (m*n) ∧ 1 < m*n ∧ rough (W x) m ∧ (m*n-1)/2 ≤ ⌊2*x⌋₊) :=
          fun h => hgate ⟨h.1, h.2.1⟩
        simp only [ite_eq_right hgate, ite_eq_right hc, norm_zero, mul_zero, le_refl]
    _ = Mf*M^2*∑ m ∈ dyad U, ∑ n ∈ dyad V,
      if Odd (m*n) ∧ 1 < m*n ∧ rough (W x) m ∧ (m*n-1)/2 ≤ ⌊2*x⌋₊ then B ((m*n-1)/2) else 0 :=
      by simp only [Finset.mul_sum]
    _ ≤ Mf*M^2*(Real.exp (2*Real.sqrt (L x))*∑ u ∈ Finset.Icc 1 ⌊2*x⌋₊, B u) :=
      mul_le_mul_of_nonneg_left (discarded_rough_pair_mass_bound D x jstar U V sigma hx) (by positivity)
    _ = _ := by ring


end Erdos821.P6Off
