import Erdos821.P6Off.PreCauchyPairs

noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

def slotPhase (D : BandData) {x : ℝ} {jstar : ℕ} (z : D.Lists x jstar)
    (nu : ProcessedIndex D x jstar → ℝ) : ℂ :=
  ∏ i, Erdos821.Blueprint.Analytic.mellin (z (processedSlot D x jstar i)).val (nu i)

theorem sum_slot_fibers {ι : Type*} [Fintype ι] (s : Finset ℕ) (p : ι → Prop) [DecidablePred p]
    (v : ι → ℕ) (w : ι → ℂ) :
    (∑ e ∈ s, ∑ z : ι, if p z ∧ v z = e then w z else 0) =
      ∑ z : ι, if p z ∧ v z ∈ s then w z else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hp : p z
  · simp only [hp, true_and]
    rw [Finset.sum_ite_eq]
  · simp [hp]

theorem mellin_nat_factor (u e : ℕ) (rho : ℝ) (hu : 0 < u) (he : 0 < e) (hd : e ∣ u) :
    Erdos821.Blueprint.Analytic.mellin e rho * Erdos821.Blueprint.Analytic.mellin (u/e:ℕ) rho =
      Erdos821.Blueprint.Analytic.mellin u rho := by
  have hq : 0 < u/e := Nat.div_pos (Nat.le_of_dvd hu hd) he
  have hprod : (e:ℝ)*(u/e:ℕ) = u := by exact_mod_cast Nat.mul_div_cancel' hd
  have hep : (0:ℝ) < e := by exact_mod_cast he
  have hqp : (0:ℝ) < (u/e:ℕ) := by exact_mod_cast hq
  have hlog : Real.log (u:ℝ) = Real.log (e:ℝ)+Real.log (u/e:ℕ) := by
    calc
      _ = Real.log ((e:ℝ)*(u/e:ℕ)) := congrArg Real.log hprod.symm
      _ = _ := Real.log_mul hep.ne' hqp.ne'
  unfold Erdos821.Blueprint.Analytic.mellin
  rw [← Complex.exp_add, hlog]
  congr 1
  push_cast
  ring

def slotBranchValue (D : BandData) (x : ℝ) (jstar : ℕ) (Cs K0 U V : ℝ)
    (alpha beta : ℕ → ℂ) (delta : ProcessedIndex D x jstar → Bool)
    (xi : ProcessedIndex D x jstar → ℝ) (t : ℝ) : ℂ :=
  let E := U*L x^(-K0)
  e (Real.log E*∑ i, xi i/processedScale D x jstar i)*e (-t*Real.log x)*
    pairSum U V (fun u => (factorialNormalization D x : ℂ)*
      Erdos821.Blueprint.Analytic.mellin u (2*Real.pi*t)*
        ∑ z : D.Lists x jstar,
          if D.listProduct z = groupFreePart (D.groups x) u ∧
            processedFactor D z delta ∈ Finset.Icc ⌈E*L x^(-Cs)⌉₊ ⌊E⌋₊ then
            (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℂ)*
              slotPhase D z (branchFrequency D x jstar delta xi)
          else 0) alpha beta

theorem branchSeparatedValue_eq_slotBranchValue (hsplit : SlotCoefficientSplitTask)
    (D : BandData) (x : ℝ) (jstar : ℕ) (Cs K0 U V : ℝ)
    (alpha beta : ℕ → ℂ) (delta : ProcessedIndex D x jstar → Bool)
    (xi : ProcessedIndex D x jstar → ℝ) (t : ℝ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (hdisjoint : ∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g))
    (hfree : ∀ p : ℕ, rough (W x) p → GroupFree (D.groups x) p)
    (hepos : ∀ e ∈ Finset.Icc ⌈U*L x^(-K0)*L x^(-Cs)⌉₊ ⌊U*L x^(-K0)⌋₊, 0 < e) :
    branchSeparatedValue D x jstar Cs K0 U V alpha beta delta xi t =
      slotBranchValue D x jstar Cs K0 U V alpha beta delta xi t := by
  let E := U*L x^(-K0)
  let se := Finset.Icc ⌈E*L x^(-Cs)⌉₊ ⌊E⌋₊
  let nu := branchFrequency D x jstar delta xi
  have hcoeff (u : ℕ) (hu : 0 < u) :
      (∑ e ∈ se, if e ∣ u then
        (factorialNormalization D x : ℂ)*Erdos821.Blueprint.Analytic.mellin e (2*Real.pi*t)*
          processedCoefficient D x jstar delta true nu e *
          hCoefficient D.geometry (D.groups x) x
            (Real.exp (D.c₁*D.scale x jstar)) (Real.exp (D.c₂*D.scale x jstar))
            (2*Real.pi*t) 0 (processedCoefficient D x jstar delta false nu) (u/e)
        else 0) =
      (factorialNormalization D x : ℂ)*Erdos821.Blueprint.Analytic.mellin u (2*Real.pi*t)*
        ∑ z : D.Lists x jstar,
          if D.listProduct z = groupFreePart (D.groups x) u ∧ processedFactor D z delta ∈ se then
            (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℂ)*slotPhase D z nu else 0 := by
    refine Eq.trans ?_ (congrArg
      (fun c : ℂ => (factorialNormalization D x : ℂ)*Erdos821.Blueprint.Analytic.mellin u (2*Real.pi*t)*c)
      (sum_slot_fibers se (fun z : D.Lists x jstar => D.listProduct z = groupFreePart (D.groups x) u)
      (fun z => processedFactor D z delta)
      (fun z => (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℂ)*slotPhase D z nu)))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hep : 0 < e := hepos e he
    have hs := hsplit D x jstar hj hr hdisjoint hfree delta nu u e hu hep
    change _ = (factorialNormalization D x : ℂ)*Erdos821.Blueprint.Analytic.mellin u (2*Real.pi*t)*
      (∑ z : D.Lists x jstar, if D.listProduct z = groupFreePart (D.groups x) u ∧ processedFactor D z delta = e then
        (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℂ)*
          ∏ i, Erdos821.Blueprint.Analytic.mellin (z (processedSlot D x jstar i)).val (nu i) else 0)
    rw [hs]
    by_cases hd : e ∣ u
    · simp only [if_pos hd, hCoefficient]
      have hm := mellin_nat_factor u e (2*Real.pi*t) hu hep hd
      calc
        _ = (factorialNormalization D x : ℂ)*
            (Erdos821.Blueprint.Analytic.mellin e (2*Real.pi*t)*
              Erdos821.Blueprint.Analytic.mellin (u/e:ℕ) (2*Real.pi*t))*
            (processedCoefficient D x jstar delta true nu e*
              (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) (u/e) : ℂ)*
              roughCore x (Real.exp (D.c₁*D.scale x jstar)) (Real.exp (D.c₂*D.scale x jstar)) 0
                (processedCoefficient D x jstar delta false nu) (groupFreePart (D.groups x) (u/e))) := by ring
        _ = _ := by rw [hm]
    · simp [hd]
  unfold branchSeparatedValue slotBranchValue
  dsimp only
  congr 1
  rw [separatedSum_as_pairSum _ _ _ _ _ _ _ _ hepos]
  unfold pairSum
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hgate
  · exact congrArg (fun c : ℂ => c*alpha m*beta n)
      (hcoeff _ (odd_shift_identity _ hgate.1 hgate.2).1)
  · rfl


end Erdos821.P6Off
