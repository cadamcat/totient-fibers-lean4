import Erdos821.S56.SlotFrequencies
import Erdos821.S56.GeometricScales
import Erdos821.S56.SplittingScale

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem slot_frequency_bound (n : ℕ) (s xi : Fin n → ℝ) (delta : Fin n → Bool)
    (A smin : ℝ) (hA : 0 ≤ A) (hsmin : 0 < smin)
    (hs : ∀ i, smin ≤ s i) (hxi : ∀ i, |xi i| ≤ A) (t : Fin n) :
    |Erdos821.S56.slotFrequency s xi delta t| ≤ ((n : ℝ) + 1) * (A / smin) := by
  classical
  have hratio (i : Fin n) : |xi i / s i| ≤ A / smin := by
    have hsi : 0 < s i := hsmin.trans_le (hs i)
    rw [abs_div, abs_of_pos hsi]
    exact (div_le_div_of_nonneg_right (hxi i) hsi.le).trans
      (div_le_div_of_nonneg_left hA hsmin (hs i))
  have hAn : 0 ≤ A / smin := div_nonneg hA hsmin.le
  let q := Finset.univ.filter (fun i : Fin n => t.val < i.val)
  have hsum : |∑ i ∈ q, xi i / s i| ≤ (n : ℝ) * (A / smin) := by
    have hcard : (q.card : ℝ) ≤ n := by
      exact_mod_cast ((Finset.card_filter_le _ _).trans (by simp : (Finset.univ : Finset (Fin n)).card ≤ n))
    calc
      _ ≤ ∑ i ∈ q, |xi i / s i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ q, A / smin := Finset.sum_le_sum (fun i _ => hratio i)
      _ = q.card * (A / smin) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hAn
  by_cases hd : delta t = true
  · simp only [Erdos821.S56.slotFrequency, hd, ↓reduceIte, one_mul]
    calc
      _ ≤ |-xi t / s t| + |∑ i ∈ q, xi i / s i| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (-xi t / s t) (∑ i ∈ q, xi i / s i)
      _ ≤ A / smin + (n : ℝ) * (A / smin) := by
        exact add_le_add (by simpa only [neg_div, abs_neg] using hratio t) hsum
      _ = _ := by ring
  · simp only [Erdos821.S56.slotFrequency, hd, Bool.false_eq_true, ↓reduceIte,
      zero_mul, sub_zero, neg_div, abs_neg]
    exact (hratio t).trans (by
      have hn := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hAn
      nlinarith)

theorem eventually_processed_count_le_L (D : BandData) (hD : D.Valid) :
    ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ, ((pureIndices D x jstar).card : ℝ) ≤ L x := by
  obtain ⟨C, hC, hc⟩ := processed_card_bound D hD
  filter_upwards [hc, loglog_le_small_log 2 C (by norm_num) hC.le] with x hx hT
  intro jstar
  exact (hx jstar).trans (by simpa using hT)

/-- A fixed polynomial frequency bound suffices for the endpoint interface.
It is weaker than the paper's O(L/T), and avoids any new dependence on K₀. -/
theorem slot_frequencies_polylog (D : BandData) (hD : D.Valid) :
    ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ, ∀ xi : ProcessedIndex D x jstar → ℝ,
      (∀ i, |xi i| ≤ L x) → ∀ delta : ProcessedIndex D x jstar → Bool,
        ∀ t, |2 * Real.pi * Erdos821.S56.slotFrequency (processedScale D x jstar) xi delta t| ≤
          L x ^ (4 : ℕ) := by
  have hdata := hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, hcmin, hcmax, hevent⟩ := hdata
  have hlarge := tendsto_L.eventually (eventually_ge_atTop (max (max 1 (2 / cmin)) (2 * Real.pi)))
  filter_upwards [hevent, eventually_processed_count_le_L D hD, hlarge,
    tendsto_T.eventually (eventually_ge_atTop 1)] with x hx hn hL hT1
  have hL1 : 1 ≤ L x := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLp : 0 < L x := zero_lt_one.trans_le hL1
  intro jstar xi hxi delta t
  have hs (i : ProcessedIndex D x jstar) : cmin ≤ processedScale D x jstar i := by
    have hscale := scale_antitone D hD x hLp (processedSlot D x jstar i).1.val (D.last x)
      (Nat.le_of_lt_succ (processedSlot D x jstar i).1.isLt)
    have hterm := hx.2.1
    dsimp [processedScale]
    nlinarith
  have hb := slot_frequency_bound _ (processedScale D x jstar) xi delta (L x) cmin hLp.le hcmin hs hxi t
  have hcount := hn jstar
  have hminL : 2 / cmin ≤ L x := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hpiL : 2 * Real.pi ≤ L x := (le_max_right _ _).trans hL
  have hcube : |Erdos821.S56.slotFrequency (processedScale D x jstar) xi delta t| ≤ L x ^ 3 := by
    have hnum : (2 : ℝ) ≤ cmin * L x := by
      simpa only [mul_comm] using (div_le_iff₀ hcmin).mp hminL
    have hden : ((pureIndices D x jstar).card : ℝ) + 1 ≤ 2 * L x := by linarith
    apply hb.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hcmin).mpr
    have hnum3 := mul_le_mul_of_nonneg_right hnum (sq_nonneg (L x))
    have hden2 := mul_le_mul_of_nonneg_right hden hLp.le
    nlinarith
  rw [abs_mul, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]
  exact (mul_le_mul_of_nonneg_left hcube (by positivity)).trans (by
    have h := mul_le_mul_of_nonneg_right hpiL (pow_nonneg hLp.le 3)
    simpa [pow_succ, mul_comm] using h)


end Erdos821.S56Core
