import Erdos821.P6Off.FrequencyDyad

noncomputable section
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem frequencyDyad_norm_le (P : Geometry) (G : PrimeGroups)
    (x U Z lo hi rho sigma : ℝ) (xi : Fin 3 → ℝ) (N r : ℕ) [NeZero r]
    (k : ℤ) (c alpha : ℕ → ℂ) (hU : 0 < U) (hZ : 0 < Z) (hN : 2 * Z ≤ (N : ℝ))
    (hunit : ∀ m, alpha m ≠ 0 → IsUnit (m : ZMod r)) (M : ℝ)
    (hbound : ∀ chi : DirichletCharacter ℂ r,
      ‖dyadicSeparatedCorrelation P G x U lo hi rho sigma (2 * Real.pi * xi 0)
        (2 * Real.pi * xi 1) (2 * Real.pi * xi 2) Z c alpha r chi k‖ ≤ M) :
    ‖frequencyDyad P G x U Z lo hi rho sigma xi N r k c alpha‖ ≤ M := by
  rw [frequencyDyad_eq_character_average P G x U Z lo hi rho sigma xi N r k c alpha hU hZ hN hunit,
    mul_assoc, norm_mul, norm_phaseScalar, one_mul]
  exact norm_character_average_le r _ M hbound

/-- A single ShiftEstimate application bounds the Fourier main range on each
dyad, uniformly in every character and frequency satisfying the fixed bounds. -/
theorem frequencyDyad_bound (hshift : ShiftEstimate) (P : Geometry)
    (D C tau eta : ℝ) (hD : 0 < D) (hC : 0 < C) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (U Z lo hi rho sigma : ℝ) (xi : Fin 3 → ℝ)
        (N r : ℕ) (hr : 0 < r) (k : ℤ) (c alpha : ℕ → ℂ),
        Admissible P x G → 0 < U → 0 < Z → 2 * Z ≤ (N : ℝ) →
        (∀ chi : DirichletCharacter ℂ r,
          EndpointBound x C tau eta
            (shiftEndpoint U lo hi rho sigma (-2 * Real.pi * xi 1) c alpha r hr chi) ∧
          EndpointBound x C tau eta
            (shiftEndpoint U lo hi rho sigma (2 * Real.pi * xi 0) c alpha r hr chi)) →
        k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
        x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
        |rho + 2 * Real.pi * xi 2| ≤ L x ^ C → |rho| ≤ L x ^ C →
        (∀ m, alpha m ≠ 0 → GroupFree G m) →
        (∀ m, alpha m ≠ 0 → IsUnit (m : ZMod r)) →
        discrepancy x B (restricted U alpha) →
        ‖frequencyDyad P G x U Z lo hi rho sigma xi N r k c alpha‖ ≤ K * Z * L x ^ (-D) := by
  obtain ⟨B, K, hB, hK, hb⟩ := separated_correlation_bound hshift P D C tau eta hD hC
  refine ⟨B, K, hB, hK, hb.mono ?_⟩
  intro x hb G U Z lo hi rho sigma xi N r hr k c alpha hG hU hZ hN hE hk hkbound hZlo hZhi hfreq hrho hfree hunit hdisc
  letI : NeZero r := ⟨hr.ne'⟩
  apply frequencyDyad_norm_le P G x U Z lo hi rho sigma xi N r k c alpha hU hZ hN hunit
  intro chi
  have hF := (hE chi).1
  have hH := (hE chi).2
  have hbchi := hb G U lo hi rho sigma (2 * Real.pi * xi 0) (2 * Real.pi * xi 1)
    (2 * Real.pi * xi 2) Z c alpha r hr chi k hG (by simpa only [neg_mul] using hF) hH
    hk hkbound hZlo hZhi hZ hfreq hrho hfree hdisc
  exact hbchi


end Erdos821.P6Off
