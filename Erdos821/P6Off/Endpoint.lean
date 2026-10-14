import Erdos821.P6Off.Convolution
import Erdos821.P6Off.Discrepancy
import Erdos821.P6Off.Rough
import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem groupFreePart_dvd (G : PrimeGroups) (n : ℕ) (hn : n ≠ 0) :
    groupFreePart G n ∣ n := by
  calc
    _ ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Finset.prod_dvd_prod_of_subset _ _ (fun p => p ^ n.factorization p)
        Finset.sdiff_subset
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

theorem groupFreePart_div (G : PrimeGroups) (n m : ℕ)
    (hn : n ≠ 0) (hm : m ∣ n) (hfree : GroupFree G m) :
    groupFreePart G n = m * groupFreePart G (n / m) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by intro h; apply hn; simpa [h] using hm)
  have hhpos : 0 < n / m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hm) hmpos
  conv_lhs => rw [← Nat.mul_div_cancel' hm]
  exact groupFreePart_mul G m (n / m) hmpos hhpos hfree

/-- Group-free m coefficients make the endpoint convolution over actual
integer divisors identical to the convolution over the outside part. -/
theorem endpoint_as_actual_convolution (G : PrimeGroups) (x : ℝ) (F : Endpoint) (n : ℕ)
    (hn : n ≠ 0) (hfree : ∀ m, F.alpha m ≠ 0 → GroupFree G m) :
    endpoint G x F n =
      ∑ mh ∈ n.divisorsAntidiagonal,
        (F.alpha mh.1 * F.chi (mh.1 : ZMod F.modulus) * mellin mh.1 F.sigma₀) *
          roughCore x F.lo F.hi F.sigma₁ F.residual (groupFreePart G mh.2) := by
  let a := fun m => F.alpha m * F.chi (m : ZMod F.modulus) * mellin m F.sigma₀
  rw [endpoint_as_convolution]
  change (∑ mh ∈ (groupFreePart G n).divisorsAntidiagonal,
    a mh.1 * roughCore x F.lo F.hi F.sigma₁ F.residual mh.2) =
      ∑ mh ∈ n.divisorsAntidiagonal,
        a mh.1 * roughCore x F.lo F.hi F.sigma₁ F.residual (groupFreePart G mh.2)
  rw [Nat.sum_divisorsAntidiagonal (fun m h => a m * roughCore x F.lo F.hi F.sigma₁ F.residual h),
    Nat.sum_divisorsAntidiagonal (fun m h => a m * roughCore x F.lo F.hi F.sigma₁ F.residual (groupFreePart G h))]
  have hsub : (groupFreePart G n).divisors ⊆ n.divisors :=
    Nat.divisors_subset_of_dvd hn (groupFreePart_dvd G n hn)
  calc
    _ = ∑ m ∈ (groupFreePart G n).divisors,
        a m * roughCore x F.lo F.hi F.sigma₁ F.residual (groupFreePart G (n / m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hα : F.alpha m = 0
      · simp [a, hα]
      · have hmdiv : m ∣ n := Nat.dvd_of_mem_divisors (hsub hm)
        have hmpos : 0 < m := Nat.pos_of_ne_zero (by intro h; apply hn; simpa [h] using hmdiv)
        have heq := groupFreePart_div G n m hn hmdiv (hfree m hα)
        rw [heq, Nat.mul_div_cancel_left _ hmpos]
    _ = ∑ m ∈ n.divisors,
        a m * roughCore x F.lo F.hi F.sigma₁ F.residual (groupFreePart G (n / m)) := by
      apply Finset.sum_subset hsub
      intro m hm hmnot
      have hα : F.alpha m = 0 := by
        by_contra hα
        have heq := groupFreePart_div G n m hn (Nat.dvd_of_mem_divisors hm) (hfree m hα)
        apply hmnot
        exact Nat.mem_divisors.mpr ⟨heq ▸ dvd_mul_right m _, groupFreePart_ne_zero G n⟩
      simp [a, hα]
    _ = _ := rfl


end Erdos821.P6Off
