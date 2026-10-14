import Erdos821.P6Off.ShiftEndpoints

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

def twistedHConvolution (P : Geometry) (G : PrimeGroups) (x U lo hi rho sigma xi : ℝ)
    (c alpha : ℕ → ℂ) (r : ℕ) (chi : DirichletCharacter ℂ r) (n : ℕ) : ℂ :=
  ∑ mh ∈ n.divisorsAntidiagonal,
    (restricted U alpha mh.1 * chi (mh.1 : ZMod r) * mellin mh.1 xi) *
      star (hCoefficient P G x lo hi rho sigma c mh.2)

def harmonicCutoff (psi : ℝ → ℂ) (t : ℝ) : ℂ := (t : ℂ) * psi t

/-- The separated determinant summand has the first endpoint conjugated and
exactly the frequencies rho+xi3 and -rho outside the endpoints. -/
theorem shifted_endpoint_product (P : Geometry) (G : PrimeGroups)
    (x U lo hi rho sigma xi1 xi2 xi3 : ℝ) (c alpha : ℕ → ℂ)
    (r : ℕ) (hr : 0 < r) (chi : DirichletCharacter ℂ r) (n n' : ℕ)
    (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hfree : ∀ m, alpha m ≠ 0 → GroupFree G m) :
    mellin n xi3 * star (twistedHConvolution P G x U lo hi rho sigma (-xi2) c alpha r chi n) *
      twistedHConvolution P G x U lo hi rho sigma xi1 c alpha r chi n' =
    mellin n (rho + xi3) * mellin n' (-rho) *
      star (endpoint G x (shiftEndpoint U lo hi rho sigma (-xi2) c alpha r hr chi) n) *
      endpoint G x (shiftEndpoint U lo hi rho sigma xi1 c alpha r hr chi) n' *
      markWeight G P.q (fun _ => P.ell) n * markWeight G P.q (fun _ => P.ell) n' := by
  unfold twistedHConvolution
  rw [← shiftEndpoint_identity P G x U lo hi rho sigma (-xi2) c alpha r hr chi n hn hfree,
    ← shiftEndpoint_identity P G x U lo hi rho sigma xi1 c alpha r hr chi n' hn' hfree]
  simp only [star_mul, star_mellin, neg_neg, star_real_cast, mellin_add]
  ac_rfl

/-- Exact harmonic normalization used by ShiftEstimate, including all signed
shift positivity guards and the literal finite z interval. -/
theorem separated_sum_eq_shiftCorrelation (P : Geometry) (G : PrimeGroups)
    (x U elo ehi rho sigma xi1 xi2 xi3 Z clo chi : ℝ) (c alpha : ℕ → ℂ)
    (r : ℕ) (hr : 0 < r) (character : DirichletCharacter ℂ r) (k : ℤ) (psi : ℝ → ℂ)
    (hZ : Z ≠ 0) (hfree : ∀ m, alpha m ≠ 0 → GroupFree G m) :
    (∑ z ∈ Finset.Icc ⌈clo * Z⌉₊ ⌊chi * Z⌋₊,
      if 0 < z ∧ 0 < (z : ℤ) + k then
        psi (z / Z) * mellin z xi3 *
          star (twistedHConvolution P G x U elo ehi rho sigma (-xi2) c alpha r character z) *
          twistedHConvolution P G x U elo ehi rho sigma xi1 c alpha r character ((z : ℤ) + k).toNat
      else 0) =
    (Z : ℂ) * shiftCorrelation P G x Z (rho + xi3) (-rho) k
      (shiftEndpoint U elo ehi rho sigma (-xi2) c alpha r hr character)
      (shiftEndpoint U elo ehi rho sigma xi1 c alpha r hr character)
      (harmonicCutoff psi) clo chi := by
  unfold shiftCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs with hz
  · have hz0 : z ≠ 0 := hz.1.ne'
    have hz'0 : ((z : ℤ) + k).toNat ≠ 0 := by omega
    have hcast : (((z : ℤ) + k).toNat : ℝ) = ((z : ℤ) + k : ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg hz.2.le
    rw [mul_assoc (psi _), mul_assoc (psi _), shifted_endpoint_product P G x U elo ehi rho sigma xi1 xi2 xi3
      c alpha r hr character z ((z : ℤ) + k).toNat hz0 hz'0 hfree]
    have hnormalize : (Z : ℂ) * (harmonicCutoff psi (z / Z) / (z : ℂ)) = psi (z / Z) := by
      unfold harmonicCutoff
      push_cast
      field_simp [show (Z : ℂ) ≠ 0 by exact_mod_cast hZ,
        show (z : ℂ) ≠ 0 by exact_mod_cast hz0]
    rw [hcast]
    push_cast
    rw [← hnormalize]
    ring
  · simp


end Erdos821.P6Off
