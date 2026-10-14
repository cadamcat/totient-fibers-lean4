import Erdos821.P6Off.Characters
import Erdos821.P6Off.Precision

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- Character orthogonality pairs the two literal determinant factors into
shifted endpoint convolutions. The original alpha is supported on units. -/
theorem character_endpoint_pairing (P : Geometry) (G : PrimeGroups)
    (x U lo hi rho sigma xi1 xi2 : ℝ) (c alpha : ℕ → ℂ)
    (r n n' : ℕ) [NeZero r] (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hunit : ∀ m, alpha m ≠ 0 → IsUnit (m : ZMod r)) :
    (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
      if m' ∣ n ∧ m ∣ n' ∧ Nat.ModEq r m m' then
        (alpha m * hCoefficient P G x lo hi rho sigma c (n / m')) *
          star (alpha m' * hCoefficient P G x lo hi rho sigma c (n' / m)) *
          mellin m xi1 * mellin m' xi2 else 0) =
    (r.totient : ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ r,
      star (twistedHConvolution P G x U lo hi rho sigma (-xi2) c alpha r chi n) *
        twistedHConvolution P G x U lo hi rho sigma xi1 c alpha r chi n' := by
  let f := fun m => if m ∣ n' then alpha m * mellin m xi1 *
    star (hCoefficient P G x lo hi rho sigma c (n' / m)) else 0
  let g := fun m => if m ∣ n then alpha m * mellin m (-xi2) *
    star (hCoefficient P G x lo hi rho sigma c (n / m)) else 0
  have hf : ∀ m, f m ≠ 0 → IsUnit (m : ZMod r) := by
    intro m hm
    apply hunit m
    intro hzero
    exact hm (by simp [f, hzero])
  have hg : ∀ m, g m ≠ 0 → IsUnit (m : ZMod r) := by
    intro m hm
    apply hunit m
    intro hzero
    exact hm (by simp [g, hzero])
  calc
    _ = ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if Nat.ModEq r m m' then f m * star (g m') else 0 := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro m' _
      by_cases hd : m' ∣ n <;> by_cases hd' : m ∣ n' <;>
        by_cases hc : Nat.ModEq r m m' <;>
        simp [f, g, hd, hd', hc, star_mul, star_mellin] <;> ring
    _ = _ := finite_character_projection r (dyad U) (dyad U) f g hf hg
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro chi _
      have hfchi : (∑ m ∈ dyad U, f m * chi (m : ZMod r)) =
          twistedHConvolution P G x U lo hi rho sigma xi1 c alpha r chi n' := by
        rw [twistedHConvolution_as_dyad P G x U lo hi rho sigma xi1 c alpha r chi n' hn']
        apply Finset.sum_congr rfl
        intro m _
        by_cases hd : m ∣ n'
        · simp only [f, hd, ite_true]
          ac_rfl
        · simp [f, hd]
      have hgchi : (∑ m ∈ dyad U, g m * chi (m : ZMod r)) =
          twistedHConvolution P G x U lo hi rho sigma (-xi2) c alpha r chi n := by
        rw [twistedHConvolution_as_dyad P G x U lo hi rho sigma (-xi2) c alpha r chi n hn]
        apply Finset.sum_congr rfl
        intro m _
        by_cases hd : m ∣ n
        · simp only [g, hd, ite_true]
          ac_rfl
        · simp [g, hd]
      rw [hfchi, hgchi]
      ac_rfl


end Erdos821.P6Off
