import Erdos821.P6Off.FrequencyDyad
import Erdos821.P6Off.FourierSum
import Erdos821.P6Off.DeterminantDyads
import Erdos821.P6Off.TailTask

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic Erdos821.S56Core

abbrev DyadIndex := ℕ × ℕ × ℕ

def dyadIndexSet (N : ℕ) (U : ℝ) : Finset DyadIndex :=
  (Finset.Icc 1 N) ×ˢ (dyad U ×ˢ dyad U)

def dyadAtomWeight (P : Geometry) (G : PrimeGroups) (x Z lo hi rho sigma : ℝ)
    (r : ℕ) (k : ℤ) (c alpha : ℕ → ℂ) (i : DyadIndex) : ℂ :=
  let z := i.1
  let m := i.2.1
  let m' := i.2.2
  if 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧ Nat.ModEq r m m' then
    (dyadicCutoff (z / Z) : ℂ) *
      (alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
        star (alpha m' * hCoefficient P G x lo hi rho sigma c (((z : ℤ) + k).toNat / m))
  else 0

def determinantAtShift (P : Geometry) (G : PrimeGroups) (x E U V Z lo hi rho sigma : ℝ)
    (N : ℕ) (k : ℤ) (etae etan : ℝ → ℝ) (c alpha : ℕ → ℂ) : ℂ :=
  ∑ z ∈ Finset.Icc 1 N, ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
    (dyadicCutoff (z / Z) : ℂ) * determinantTerm E V etae etan
      (hCoefficient P G x lo hi rho sigma c) alpha k z m m'

/-- The abstract finite Fourier sum reads the actual dyadic determinant coefficients. -/
theorem frequencySum_dyadAtoms (P : Geometry) (G : PrimeGroups)
    (x U Z lo hi rho sigma : ℝ) (N r : ℕ) (k : ℤ) (c alpha : ℕ → ℂ) (xi : Fin 3 → ℝ) :
    frequencySum (dyadIndexSet N U) (dyadAtomWeight P G x Z lo hi rho sigma r k c alpha)
      (fun i => logCoordinates U Z i.2.1 i.2.2 i.1) xi =
      frequencyDyad P G x U Z lo hi rho sigma xi N r k c alpha := by
  simp only [frequencySum, dyadIndexSet, Finset.sum_product]
  unfold frequencyDyad
  apply Finset.sum_congr rfl
  intro z _
  by_cases hzk : 0 < (z : ℤ) + k
  · simp only [hzk, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro m' _
    simp only [dyadAtomWeight, hzk, true_and]
    split_ifs <;> ring
  · simp [dyadAtomWeight, hzk]

/-- Dropping the congruence only increases the absolute Fourier-error mass. -/
theorem norm_dyadAtoms_le_absolute (P : Geometry) (G : PrimeGroups)
    (x U Z lo hi rho sigma : ℝ) (N r : ℕ) (k : ℤ) (c alpha : ℕ → ℂ) :
    (∑ i ∈ dyadIndexSet N U, ‖dyadAtomWeight P G x Z lo hi rho sigma r k c alpha i‖) ≤
      absoluteDeterminantDyad P G x U Z lo hi rho sigma N k dyadicCutoff c alpha := by
  simp only [dyadIndexSet, Finset.sum_product]
  unfold absoluteDeterminantDyad
  apply Finset.sum_le_sum
  intro z _
  apply Finset.sum_le_sum
  intro m _
  apply Finset.sum_le_sum
  intro m' _
  by_cases hzk : 0 < (z : ℤ) + k <;> by_cases hm' : m' ∣ z <;>
    by_cases hm : m ∣ ((z : ℤ) + k).toNat <;> by_cases hcong : Nat.ModEq r m m' <;>
    simp [dyadAtomWeight, hzk, hm, hm', hcong] <;> positivity

/-- Exact use of the localized pulled-back cutoff in the literal dyadic sum. -/
theorem determinantAtShift_as_weighted_cutoff (P : Geometry) (G : PrimeGroups)
    (x E U V Z lo hi rho sigma : ℝ) (N : ℕ) (k : ℤ) (etae etan : ℝ → ℝ) (c alpha : ℕ → ℂ)
    (hk : k ≠ 0) (hU : 0 < U) (hZ : 0 < Z) :
    determinantAtShift P G x E U V Z lo hi rho sigma N k etae etan c alpha =
      ∑ i ∈ dyadIndexSet N U,
        dyadAtomWeight P G x Z lo hi rho sigma (2 * k.natAbs) k c alpha i *
          pulledCutoff U V Z E k etae etan logLocalizer (logCoordinates U Z i.2.1 i.2.2 i.1) := by
  unfold determinantAtShift
  simp only [dyadIndexSet, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro m' hm'
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (Finset.mem_Icc.mp hz).1
  have hmR := (mem_dyad_iff U m).mp hm
  have hm'R := (mem_dyad_iff U m').mp hm'
  have hmpos : (0 : ℝ) < m := hU.trans_le hmR.1
  have hm'pos : (0 : ℝ) < m' := hU.trans_le hm'R.1
  by_cases hphi : dyadicCutoff (z / Z) = 0
  · simp [dyadAtomWeight, hphi]
  · have hzrange := dyadicCutoff_support hphi
    have hmr : 1 / 2 ≤ (m : ℝ) / U ∧ (m : ℝ) / U ≤ 2 := by
      constructor
      · apply (le_div_iff₀ hU).mpr
        linarith
      · apply (div_le_iff₀ hU).mpr
        linarith
    have hm'r : 1 / 2 ≤ (m' : ℝ) / U ∧ (m' : ℝ) / U ≤ 2 := by
      constructor
      · apply (le_div_iff₀ hU).mpr
        linarith
      · apply (div_le_iff₀ hU).mpr
        linarith
    rw [pulledCutoff_on_ranges U V Z E m m' z k etae etan hU hZ hmpos hm'pos hzpos
      (logLocalizer_one U Z m m' z hmr hm'r hzrange)]
    have hguard :
        (k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m') ↔
        (0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m') := ⟨And.right, fun h => ⟨hk, h⟩⟩
    simp only [dyadAtomWeight, determinantTerm, hguard]
    split_ifs <;> ring


end Erdos821.P6Off
