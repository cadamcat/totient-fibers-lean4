import Erdos821.P6Off.Task

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

set_option backward.isDefEq.respectTransparency false in
/-- Reindex three positive factors without changing the endpoint coefficient. -/
theorem triple_factor_sum (N : ℕ) (hN : N ≠ 0) (f : ℕ → ℕ → ℕ → ℂ) :
    (∑ mh ∈ N.divisorsAntidiagonal, ∑ pr ∈ mh.2.divisorsAntidiagonal,
      f mh.1 pr.1 pr.2) =
    ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
      if m * p * r = N then f m p r else 0 := by
  let s := N.divisorsAntidiagonal.sigma (fun mh => mh.2.divisorsAntidiagonal)
  let t := (((Finset.Icc 1 N).product (Finset.Icc 1 N)).product
    (Finset.Icc 1 N)).filter (fun mpr => mpr.1.1 * mpr.1.2 * mpr.2 = N)
  calc
    _ = ∑ a ∈ s, f a.1.1 a.2.1 a.2.2 := by rw [Finset.sum_sigma']
    _ = ∑ a ∈ t, f a.1.1 a.1.2 a.2 := by
      apply Finset.sum_bij (fun a _ => ((a.1.1, a.2.1), a.2.2))
      · intro a ha
        obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
        obtain ⟨heq1, _⟩ := Nat.mem_divisorsAntidiagonal.mp ha1
        obtain ⟨heq2, hpos⟩ := Nat.mem_divisorsAntidiagonal.mp ha2
        have hm : 0 < a.1.1 := Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal ha1)
        have hp : 0 < a.2.1 := Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal ha2)
        have hr : 0 < a.2.2 := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal ha2)
        have heq : a.1.1 * a.2.1 * a.2.2 = N := by rw [Nat.mul_assoc, heq2, heq1]
        have hmle : a.1.1 ≤ N := by
          rw [← heq, Nat.mul_assoc]
          exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hp hr)
        have hple : a.2.1 ≤ N := by
          rw [← heq]
          calc
            a.2.1 ≤ a.1.1 * a.2.1 := Nat.le_mul_of_pos_left _ hm
            _ ≤ a.1.1 * a.2.1 * a.2.2 := Nat.le_mul_of_pos_right _ hr
        have hrle : a.2.2 ≤ N := heq ▸ Nat.le_mul_of_pos_left _ (Nat.mul_pos hm hp)
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hm, hmle⟩,
            Finset.mem_Icc.mpr ⟨hp, hple⟩⟩, Finset.mem_Icc.mpr ⟨hr, hrle⟩⟩, heq⟩
      · intro a ha b hb hab
        obtain ⟨_, ha2⟩ := Finset.mem_sigma.mp ha
        obtain ⟨_, hb2⟩ := Finset.mem_sigma.mp hb
        have haeq := (Nat.mem_divisorsAntidiagonal.mp ha2).1
        have hbeq := (Nat.mem_divisorsAntidiagonal.mp hb2).1
        have hm : a.1.1 = b.1.1 := congrArg (fun v => v.1.1) hab
        have hp : a.2.1 = b.2.1 := congrArg (fun v => v.1.2) hab
        have hr : a.2.2 = b.2.2 := congrArg (fun v : (ℕ × ℕ) × ℕ => v.2) hab
        have hh : a.1.2 = b.1.2 := by rw [← haeq, ← hbeq, hp, hr]
        have hfirst : a.1 = b.1 := Prod.ext hm hh
        have hsecond : a.2 = b.2 := Prod.ext hp hr
        exact Sigma.ext hfirst (heq_of_eq hsecond)
      · intro b hb
        obtain ⟨hb0, heq⟩ := Finset.mem_filter.mp hb
        obtain ⟨hbmp, hbr⟩ := Finset.mem_product.mp hb0
        obtain ⟨hbm, hbp⟩ := Finset.mem_product.mp hbmp
        have hp : 0 < b.1.2 := (Finset.mem_Icc.mp hbp).1
        have hr : 0 < b.2 := (Finset.mem_Icc.mp hbr).1
        refine ⟨⟨(b.1.1, b.1.2 * b.2), (b.1.2, b.2)⟩, ?_, rfl⟩
        exact Finset.mem_sigma.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr
          ⟨by simpa [Nat.mul_assoc] using heq, hN⟩,
          Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos hp hr).ne'⟩⟩
      · intro a _
        rfl
    _ = _ := by
      simp only [t, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]

/-- The outside part is a product of positive prime powers even at n=0. -/
theorem groupFreePart_ne_zero (G : PrimeGroups) (n : ℕ) : groupFreePart G n ≠ 0 := by
  unfold groupFreePart
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).ne_zero

/-- The literal endpoint is the convolution of its original m sequence with
its rough-slot coefficient. This identity preserves every coefficient twist. -/
theorem endpoint_as_convolution (G : PrimeGroups) (x : ℝ) (F : Endpoint) (n : ℕ) :
    endpoint G x F n =
      ∑ mh ∈ (groupFreePart G n).divisorsAntidiagonal,
        (F.alpha mh.1 * F.chi (mh.1 : ZMod F.modulus) * mellin mh.1 F.sigma₀) *
          roughCore x F.lo F.hi F.sigma₁ F.residual mh.2 := by
  symm
  calc
    _ = ∑ mh ∈ (groupFreePart G n).divisorsAntidiagonal,
        ∑ pr ∈ mh.2.divisorsAntidiagonal,
          if F.lo ≤ (pr.1 : ℝ) ∧ (pr.1 : ℝ) ≤ F.hi ∧ rough (W x) pr.1 then
            F.alpha mh.1 * F.chi (mh.1 : ZMod F.modulus) * mellin mh.1 F.sigma₀ *
              mellin pr.1 F.sigma₁ * F.residual pr.2 else 0 := by
      apply Finset.sum_congr rfl
      intro mh _
      unfold roughCore
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro pr _
      split_ifs <;> ring
    _ = _ := by
      rw [triple_factor_sum _ (groupFreePart_ne_zero G n) (fun m p r =>
        if F.lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ F.hi ∧ rough (W x) p then
          F.alpha m * F.chi (m : ZMod F.modulus) * mellin m F.sigma₀ *
            mellin p F.sigma₁ * F.residual r else 0)]
      unfold endpoint
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      by_cases heq : m * p * r = groupFreePart G n
      · simp [heq]
      · simp [heq]


end Erdos821.P6Off
