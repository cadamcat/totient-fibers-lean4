import Erdos821.S56.Definitions

namespace Erdos821.S56
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem aQ_nonneg_proved (G : Geometry) (x : ℝ) (n : ℕ) : 0 ≤ aQ G x n := by
  unfold aQ
  positivity

/-- The diagonal divisor sum requires only divisor-set monotonicity. -/
theorem divisor_diagonal_proved (u : ℕ) (hu : 0 < u) :
    ∑ e ∈ u.divisors, τ (u / e) ^ (2 : ℕ) ≤ τ u ^ (3 : ℕ) := by
  calc
    _ ≤ ∑ _e ∈ u.divisors, τ u ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro e he
      have hdvd : u / e ∣ u := Nat.div_dvd_of_dvd (Nat.mem_divisors.mp he).1
      have hcard := Finset.card_le_card (Nat.divisors_subset_of_dvd hu.ne' hdvd)
      have hτ : τ (u / e) ≤ τ u := by unfold τ; exact_mod_cast hcard
      exact pow_le_pow_left₀ (by unfold τ; positivity) hτ 2
    _ = _ := by simp [τ]; ring

theorem weighted_cauchy_proved {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ (2 : ℕ) ≤
      (∑ i ∈ s, ‖a i‖ ^ (2 : ℕ)) * ∑ i ∈ s, ‖b i‖ ^ (2 : ℕ) := by
  have hn : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => a i * b i)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖))

theorem determinant_pullback_proved (m m' n e h k : ℝ) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hk : k ≠ 0) (h₁ : m * n = 2 * e * h + 1) (hinc : m' - m = 2 * e * k) :
    e = (m' - m) / (2 * k) ∧ n = (m' - m) * (m' * h) / (k * m * m') + 1 / m := by
  constructor
  · apply (eq_div_iff (mul_ne_zero (by norm_num) hk)).mpr
    nlinarith
  · symm
    calc
      _ = (m' - m) * h / (k * m) + 1 / m := by field_simp [hm, hm', hk] <;> ring
      _ = (2 * e * h + 1) / m := by rw [hinc]; field_simp [hm, hk] <;> ring
      _ = n := by apply (div_eq_iff hm).mpr; nlinarith

theorem harmonic_normalization_proved (s : Finset ℕ) (Z : ℝ) (hZ : Z ≠ 0)
    (hs : ∀ z ∈ s, z ≠ 0) (ψ : ℝ → ℂ) (f : ℕ → ℂ) :
    (∑ z ∈ s, ψ ((z : ℝ) / Z) * f z) =
      (Z : ℂ) * ∑ z ∈ s, (((z : ℝ) / Z : ℝ) : ℂ) * ψ ((z : ℝ) / Z) / (z : ℂ) * f z := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hs z hz
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ
  push_cast
  field_simp [hz', hZ']

theorem mass_to_card_proved {ι : Type*} (s : Finset ι) (f : ι → ℝ) (M : ℝ)
    (hM : 0 < M) (hf : ∀ i ∈ s, f i ≤ M) : (∑ i ∈ s, f i) / M ≤ s.card := by
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ ∑ _i ∈ s, M := Finset.sum_le_sum hf
    _ = _ := by simp

theorem proxy_cell_bounds_proved (x S : ℝ) (I : ℕ → Prop) (i : ℤ)
    (hsub : ∀ m ∈ logCell x S i, I m → Rough (W x) m)
    (hpos : 0 < ((logCell x S i).filter (Rough (W x))).card) :
    0 ≤ cellCoefficient x S I i ∧ cellCoefficient x S I i ≤ 1 ∧
    (∑ m ∈ logCell x S i, indicator I m) =
      cellCoefficient x S I i * (((logCell x S i).filter (Rough (W x))).card : ℝ) := by
  classical
  have hden : (0 : ℝ) < ((logCell x S i).filter (Rough (W x))).card := by exact_mod_cast hpos
  have hcard : ((logCell x S i).filter I).card ≤ ((logCell x S i).filter (Rough (W x))).card := by
    apply Finset.card_le_card
    intro m hm
    obtain ⟨hmem, hI⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hmem, hsub m hmem hI⟩
  refine ⟨by unfold cellCoefficient; positivity, ?_, ?_⟩
  · apply (div_le_one hden).mpr
    exact_mod_cast hcard
  · rw [cellCoefficient, div_mul_cancel₀ _ hden.ne']
    simp [indicator]


end Erdos821.S56
