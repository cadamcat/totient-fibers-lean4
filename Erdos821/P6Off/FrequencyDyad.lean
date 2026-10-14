import Erdos821.P6Off.FrequencyPairing
import Erdos821.P6Off.ZSupport
import Erdos821.P6Off.Average
import Erdos821.P6Off.ShiftBound

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic Erdos821.S56Core

def frequencyDyad (P : Geometry) (G : PrimeGroups) (x U Z lo hi rho sigma : ℝ)
    (xi : Fin 3 → ℝ) (N r : ℕ) (k : ℤ) (c alpha : ℕ → ℂ) : ℂ :=
  ∑ z ∈ Finset.Icc 1 N,
    if 0 < (z : ℤ) + k then
      (dyadicCutoff (z / Z) : ℂ) *
        ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
          if m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧ Nat.ModEq r m m' then
            (alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
              star (alpha m' * hCoefficient P G x lo hi rho sigma c (((z : ℤ) + k).toNat / m)) *
                e (∑ i, xi i * logCoordinates U Z m m' z i) else 0
    else 0

def dyadicSeparatedCorrelation (P : Geometry) (G : PrimeGroups)
    (x U lo hi rho sigma xi1 xi2 xi3 Z : ℝ) (c alpha : ℕ → ℂ)
    (r : ℕ) (chi : DirichletCharacter ℂ r) (k : ℤ) : ℂ :=
  ∑ z ∈ Finset.Icc ⌈(1 / 2 : ℝ) * Z⌉₊ ⌊2 * Z⌋₊,
    if 0 < z ∧ 0 < (z : ℤ) + k then
      (dyadicCutoff (z / Z) : ℂ) * mellin z xi3 *
        star (twistedHConvolution P G x U lo hi rho sigma (-xi2) c alpha r chi z) *
        twistedHConvolution P G x U lo hi rho sigma xi1 c alpha r chi ((z : ℤ) + k).toNat
    else 0

/-- Exact Fourier-frequency reduction on a fixed dyad, with no divisor or
congruence condition dropped. -/
theorem frequencyDyad_eq_character_average (P : Geometry) (G : PrimeGroups)
    (x U Z lo hi rho sigma : ℝ) (xi : Fin 3 → ℝ) (N r : ℕ) [NeZero r]
    (k : ℤ) (c alpha : ℕ → ℂ) (hU : 0 < U) (hZ : 0 < Z) (hN : 2 * Z ≤ (N : ℝ))
    (hunit : ∀ m, alpha m ≠ 0 → IsUnit (m : ZMod r)) :
    frequencyDyad P G x U Z lo hi rho sigma xi N r k c alpha =
      phaseScalar U Z xi * (r.totient : ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ r,
        dyadicSeparatedCorrelation P G x U lo hi rho sigma (2 * Real.pi * xi 0)
          (2 * Real.pi * xi 1) (2 * Real.pi * xi 2) Z c alpha r chi k := by
  let f := fun z : ℕ =>
    if 0 < (z : ℤ) + k then
      ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧ Nat.ModEq r m m' then
          (alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
            star (alpha m' * hCoefficient P G x lo hi rho sigma c (((z : ℤ) + k).toNat / m)) *
              e (∑ i, xi i * logCoordinates U Z m m' z i) else 0
    else 0
  have hform : frequencyDyad P G x U Z lo hi rho sigma xi N r k c alpha =
      ∑ z ∈ Finset.Icc 1 N, (dyadicCutoff (z / Z) : ℂ) * f z := by
    unfold frequencyDyad
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [f]
    split_ifs <;> simp
  rw [hform, sum_dyadic_support_interval Z hZ N hN _ dyadicCutoff_complex_support]
  unfold dyadicSeparatedCorrelation
  rw [Finset.sum_comm (s := (Finset.univ : Finset (DirichletCharacter ℂ r)))
    (t := Finset.Icc ⌈(1 / 2 : ℝ) * Z⌉₊ ⌊2 * Z⌋₊), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hzpos : 0 < z :=
    (Nat.one_le_ceil_iff.mpr (by positivity : 0 < (1 / 2 : ℝ) * Z)).trans (Finset.mem_Icc.mp hz).1
  dsimp only [f]
  by_cases hzk : 0 < (z : ℤ) + k
  · have hzk0 : ((z : ℤ) + k).toNat ≠ 0 := by omega
    simp only [hzk, hzpos, and_self, ite_true]
    rw [frequency_pair_at_z P G x U Z lo hi rho sigma xi c alpha r z
      ((z : ℤ) + k).toNat hU hZ hzpos hzk0 hunit]
    simp only [Finset.mul_sum, neg_mul]
    apply Finset.sum_congr rfl
    intro chi _
    ring
  · simp [hzk]


end Erdos821.P6Off
