import Erdos821.S9.EulerTasks
import Erdos821.S9Mask.HarmonicP

/-! Proof of the frozen `MaskHarmonicPTask`: the Boolean mask average of the allowed-prime
compensation is at most the literal `harmonicP`. -/

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.S9Mask
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core Erdos821.S56Core

theorem one_le_inv_one_sub (p : ℕ) (hp : p.Prime) : 1 ≤ (1 - 1 / (p : ℝ))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr hp1
    linarith
  rw [one_le_inv₀ hpos]
  have : 0 ≤ 1 / (p : ℝ) := by positivity
  linarith

/-- Pointwise: the allowed-prime compensation below `z` is at most the full product over
the allowed primes. -/
theorem allowed_comp_le (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (D : ℕ) (z : ℝ)
    (allow : PermissionIndex R → Bool) :
    (∏ p ∈ primesUpTo z, pairAComp p D (permissionAllowed R allow)) ≤
      ∏ p : PermissionIndex R, (if allow p then (1 - 1 / ((p : ℕ) : ℝ))⁻¹ else 1) := by
  classical
  set A := permissionAllowed R allow with hAdef
  have hAR : A ⊆ R := by
    intro p hp
    obtain ⟨p', -, rfl⟩ := Finset.mem_image.mp hp
    exact p'.2
  have hprimeUp : ∀ p ∈ primesUpTo z, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  calc
    (∏ p ∈ primesUpTo z, pairAComp p D A) ≤
        ∏ p ∈ primesUpTo z, (if p ∈ A then (1 - 1 / (p : ℝ))⁻¹ else 1) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        unfold pairAComp
        split
        · exact le_trans zero_le_one (one_le_inv_one_sub p (hprimeUp p hp))
        · exact zero_le_one
      · intro p hp
        unfold pairAComp
        by_cases hpA : p ∈ A
        · by_cases hpD : p ∣ D
          · have h1 := one_le_inv_one_sub p (hprimeUp p hp)
            simp only [hpA, hpD, not_true_eq_false, and_false, ite_false, ite_true]
            exact h1
          · simp [hpA, hpD]
        · simp [hpA]
    _ = ∏ p ∈ primesUpTo z ∩ A, (1 - 1 / (p : ℝ))⁻¹ := Finset.prod_ite_mem _ _ _
    _ ≤ ∏ p ∈ A, (1 - 1 / (p : ℝ))⁻¹ := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ Finset.inter_subset_right
      · intro p hp
        exact le_trans zero_le_one
          (one_le_inv_one_sub p (hR p (hAR (Finset.mem_inter.mp hp).2)))
      · intro p hp _
        exact one_le_inv_one_sub p (hR p (hAR hp))
    _ = ∏ p ∈ R.attach.filter (fun p => allow p = true), (1 - 1 / ((p : ℕ) : ℝ))⁻¹ := by
      rw [hAdef, permissionAllowed, Finset.prod_image]
      intro a _ b _ h
      exact Subtype.ext h
    _ = ∏ p : PermissionIndex R, (if allow p then (1 - 1 / ((p : ℕ) : ℝ))⁻¹ else 1) := by
      rw [Finset.prod_filter, Finset.univ_eq_attach]

/-- Averaging the Boolean masks gives the permission Euler product over `R`. -/
theorem mask_average_le (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (D : ℕ) (z : ℝ) :
    (∑ allow : PermissionIndex R → Bool,
      permissionMaskProbability R q allow *
        ∏ p ∈ primesUpTo z, pairAComp p D (permissionAllowed R allow)) ≤
      ∏ p ∈ R, (1 + q / ((p : ℝ) - 1)) := by
  classical
  calc
    _ ≤ ∑ allow : PermissionIndex R → Bool,
          permissionMaskProbability R q allow *
            ∏ p : PermissionIndex R, (if allow p then (1 - 1 / ((p : ℕ) : ℝ))⁻¹ else 1) := by
      apply Finset.sum_le_sum
      intro allow _
      apply mul_le_mul_of_nonneg_left (allowed_comp_le R hR D z allow)
      unfold permissionMaskProbability
      apply Finset.prod_nonneg
      intro p _
      split
      · exact hq0
      · linarith
    _ = ∏ p : PermissionIndex R, ∑ b : Bool,
          (if b then q else 1 - q) * (if b then (1 - 1 / ((p : ℕ) : ℝ))⁻¹ else 1) := by
      unfold permissionMaskProbability
      rw [Fintype.prod_sum (κ := fun _ : PermissionIndex R => Bool)
        (f := fun p b => (if b then q else 1 - q) *
          (if b then (1 - 1 / ((p : ℕ) : ℝ))⁻¹ else 1))]
      apply Finset.sum_congr rfl
      intro allow _
      rw [← Finset.prod_mul_distrib]
    _ = ∏ p : PermissionIndex R, (1 + q / (((p : ℕ) : ℝ) - 1)) := by
      apply Finset.prod_congr rfl
      intro p _
      have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast (hR p p.2).one_lt
      have hpm : ((p : ℕ) : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by linarith
      have hsub : 1 - 1 / ((p : ℕ) : ℝ) = (((p : ℕ) : ℝ) - 1) / ((p : ℕ) : ℝ) := by
        field_simp
      simp only [Fintype.sum_bool, ite_true, ite_false, Bool.false_eq_true, mul_one]
      rw [hsub, inv_div]
      field_simp
      ring
    _ = ∏ p ∈ R, (1 + q / ((p : ℝ) - 1)) :=
      Finset.prod_coe_sort R (fun p => 1 + q / ((p : ℝ) - 1))

theorem MaskHarmonicPTask_proof : Erdos821.S56Core.MaskHarmonicPTask := by
  intro δ C hC
  obtain ⟨hValid, -, -, -, -, -, -, -, -, -, hell, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, -, cmin, cmax, -, -, hv⟩ := hValid
  filter_upwards [hv] with x hx
  intro R D z hR
  set G := C.bands.groups x with hG
  set q := C.bands.geometry.q with hqdef
  have hq0 : 0 < q := C.bands.geometry.damping.1
  have hq1 : q < 1 := C.bands.geometry.damping.2
  have hmass : ∀ g, 0 < mass G g := fun g =>
    lt_of_lt_of_le C.bands.geometry.positive.2.2.1 (hx.1.2.2.1 g).1
  have hgps : groupPrimeSet G = gps G := rfl
  rw [hgps] at hR
  have hRprime : ∀ p ∈ R, p.Prime := fun p hp => gps_prime G p (hR hp)
  calc
    _ ≤ ∏ p ∈ R, (1 + q / ((p : ℝ) - 1)) :=
      mask_average_le R hRprime q hq0.le hq1.le D z
    _ ≤ ∏ p ∈ gps G, (1 + q / ((p : ℝ) - 1)) := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hR
      · intro p hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (hRprime p hp).one_lt
        exact add_nonneg zero_le_one (div_nonneg hq0.le (by linarith))
      · intro p hp _
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (gps_prime G p hp).one_lt
        have : 0 ≤ q / ((p : ℝ) - 1) := div_nonneg hq0.le (by linarith)
        linarith
    _ ≤ C.bands.harmonicP x := euler_le_harmonicP C.bands x hell hmass

end Erdos821.S9Mask

/-- Exported proof of the frozen task, in the task's namespace. -/
theorem Erdos821.S56Core.MaskHarmonicPTask_proof : Erdos821.S56Core.MaskHarmonicPTask :=
  Erdos821.S9Mask.MaskHarmonicPTask_proof

example : Erdos821.S56Core.MaskHarmonicPTask := Erdos821.S56Core.MaskHarmonicPTask_proof

