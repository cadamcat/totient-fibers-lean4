import Erdos821.S56.CauchyDiagonal

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core

/-- Cauchy in (e,n), with a smooth enlargement and outside factor 2EV. -/
theorem smoothed_cauchy (emin E U V M : ℝ) (ae ah alpha beta : ℕ → ℂ)
    (etae etan : ℝ → ℝ) (hemin : 1 ≤ emin) (hE : 0 < E) (hV : 1 ≤ V)
    (hM : 0 ≤ M) (hae : ∀ e, ‖ae e‖ ≤ M) (hbeta : ∀ n, ‖beta n‖ ≤ M)
    (hetae : ∀ y, 0 ≤ etae y) (hetan : ∀ y, 0 ≤ etan y)
    (hecover : ∀ e ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊, 1 ≤ etae (e / E))
    (hncover : ∀ n ∈ dyad V, 1 ≤ etan (n / V)) :
    ‖separatedSum emin E U V ae ah alpha beta‖ ^ 2 ≤
      2 * E * V * M ^ 4 * smoothedSquare E U V etae etan ah alpha := by
  let se := Finset.Icc ⌈emin⌉₊ ⌊E⌋₊
  let sn := dyad V
  let be := Finset.Icc 1 ⌊2 * E⌋₊
  let bn := Finset.Icc 1 ⌊4 * V⌋₊
  have hepos (e : ℕ) (he : e ∈ se) : 1 ≤ e := by
    have h := Nat.ceil_le.mp (Finset.mem_Icc.mp he).1
    exact_mod_cast hemin.trans h
  have hnlo (n : ℕ) (hn : n ∈ sn) : 1 ≤ n := by
    have h := Nat.ceil_le.mp (Finset.mem_Ico.mp hn).1
    exact_mod_cast hV.trans h
  have hnhi (n : ℕ) (hn : n ∈ sn) : (n : ℝ) < 2 * V :=
    Nat.lt_ceil.mp (Finset.mem_Ico.mp hn).2
  have hse : se ⊆ be := by
    intro e he
    refine Finset.mem_Icc.mpr ⟨hepos e he, ?_⟩
    exact (Finset.mem_Icc.mp he).2.trans (Nat.floor_mono (by linarith : E ≤ 2 * E))
  have hsn : sn ⊆ bn := by
    intro n hn
    refine Finset.mem_Icc.mpr ⟨hnlo n hn, Nat.le_floor ?_⟩
    exact (hnhi n hn).le.trans (by linarith)
  have hcarde : (se.card : ℝ) ≤ E := by
    have hs : se ⊆ Finset.Icc 1 ⌊E⌋₊ := by
      intro e he
      exact Finset.mem_Icc.mpr ⟨hepos e he, (Finset.mem_Icc.mp he).2⟩
    have hc : se.card ≤ ⌊E⌋₊ := by simpa using Finset.card_le_card hs
    exact (by exact_mod_cast hc : (se.card : ℝ) ≤ ⌊E⌋₊).trans (Nat.floor_le hE.le)
  have hcardn : (sn.card : ℝ) ≤ 2 * V := by
    have hs : sn ⊆ Finset.Icc 1 ⌊2 * V⌋₊ := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨hnlo n hn, Nat.le_floor (hnhi n hn).le⟩
    have hc : sn.card ≤ ⌊2 * V⌋₊ := by simpa using Finset.card_le_card hs
    exact (by exact_mod_cast hc : (sn.card : ℝ) ≤ ⌊2 * V⌋₊).trans (Nat.floor_le (by linarith))
  have hcoeff : (se.card : ℝ) * sn.card * M ^ 4 ≤ 2 * E * V * M ^ 4 := by
    have h := mul_le_mul hcarde hcardn (Nat.cast_nonneg sn.card : (0 : ℝ) ≤ sn.card) hE.le
    have h' := mul_le_mul_of_nonneg_right h (pow_nonneg hM 4)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h'
  let f : ℕ → ℕ → ℝ := fun e n => etae (e / E) * etan (n / V) * ‖innerSum U ah alpha e n‖ ^ 2
  have hf (e n : ℕ) : 0 ≤ f e n :=
    mul_nonneg (mul_nonneg (hetae _) (hetan _)) (sq_nonneg _)
  have hsecond : (∑ e ∈ se, ∑ n ∈ sn, ‖innerSum U ah alpha e n‖ ^ 2) ≤
      smoothedSquare E U V etae etan ah alpha := by
    calc
      _ ≤ ∑ e ∈ se, ∑ n ∈ sn, f e n := by
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro n hn
        have hw := mul_le_mul (hecover e he) (hncover n hn) (by norm_num : (0 : ℝ) ≤ 1) (hetae _)
        have h := mul_le_mul_of_nonneg_right hw (sq_nonneg (‖innerSum U ah alpha e n‖))
        simpa only [one_mul] using h
      _ ≤ ∑ e ∈ be, ∑ n ∈ sn, f e n :=
        Finset.sum_le_sum_of_subset_of_nonneg hse (fun e _ _ => Finset.sum_nonneg (fun n _ => hf e n))
      _ ≤ ∑ e ∈ be, ∑ n ∈ bn, f e n := Finset.sum_le_sum (fun e _ =>
        Finset.sum_le_sum_of_subset_of_nonneg hsn (fun n _ _ => hf e n))
      _ = _ := rfl
  have hsum0 : 0 ≤ ∑ e ∈ se, ∑ n ∈ sn, ‖innerSum U ah alpha e n‖ ^ 2 := by positivity
  have hfac0 : 0 ≤ 2 * E * V * M ^ 4 := by positivity
  exact (separated_cauchy emin E U V M ae ah alpha beta hM hae hbeta).trans
    ((mul_le_mul_of_nonneg_right hcoeff hsum0).trans
      (mul_le_mul_of_nonneg_left hsecond hfac0))


end Erdos821.S56Core
