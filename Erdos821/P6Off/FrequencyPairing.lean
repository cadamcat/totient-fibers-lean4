import Erdos821.P6Off.CharacterPairing
import Erdos821.P6Off.Phases

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- A logarithmic Fourier atom in the literal determinant sum becomes the
character average of the two shifted endpoint convolutions. -/
theorem frequency_pair_at_z (P : Geometry) (G : PrimeGroups)
    (x U Z lo hi rho sigma : ℝ) (xi : Fin 3 → ℝ) (c alpha : ℕ → ℂ)
    (r n n' : ℕ) [NeZero r] (hU : 0 < U) (hZ : 0 < Z) (hn : 0 < n) (hn' : n' ≠ 0)
    (hunit : ∀ m, alpha m ≠ 0 → IsUnit (m : ZMod r)) :
    (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
      if m' ∣ n ∧ m ∣ n' ∧ Nat.ModEq r m m' then
        (alpha m * hCoefficient P G x lo hi rho sigma c (n / m')) *
          star (alpha m' * hCoefficient P G x lo hi rho sigma c (n' / m)) *
          e (∑ i, xi i * logCoordinates U Z m m' n i) else 0) =
    phaseScalar U Z xi * mellin n (2 * Real.pi * xi 2) * (r.totient : ℂ)⁻¹ *
      ∑ chi : DirichletCharacter ℂ r,
        star (twistedHConvolution P G x U lo hi rho sigma (-2 * Real.pi * xi 1) c alpha r chi n) *
          twistedHConvolution P G x U lo hi rho sigma (2 * Real.pi * xi 0) c alpha r chi n' := by
  calc
    _ = phaseScalar U Z xi * mellin n (2 * Real.pi * xi 2) *
        (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
          if m' ∣ n ∧ m ∣ n' ∧ Nat.ModEq r m m' then
            (alpha m * hCoefficient P G x lo hi rho sigma c (n / m')) *
              star (alpha m' * hCoefficient P G x lo hi rho sigma c (n' / m)) *
              mellin m (2 * Real.pi * xi 0) * mellin m' (2 * Real.pi * xi 1) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m' hm'
      have hmpos : (0 : ℝ) < m := hU.trans_le ((mem_dyad_iff U m).mp hm).1
      have hm'pos : (0 : ℝ) < m' := hU.trans_le ((mem_dyad_iff U m').mp hm').1
      split_ifs
      · rw [e_logCoordinates xi U Z m m' n hU hZ hmpos hm'pos (by exact_mod_cast hn)]
        ring
      · simp
    _ = _ := by
      rw [character_endpoint_pairing P G x U lo hi rho sigma (2 * Real.pi * xi 0)
        (2 * Real.pi * xi 1) c alpha r n n' hn.ne' hn' hunit]
      simp only [neg_mul, mul_assoc]


end Erdos821.P6Off
