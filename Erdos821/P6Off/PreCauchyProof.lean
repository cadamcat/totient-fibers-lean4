import Erdos821.P6Off.PreCauchyIntegration
import Erdos821.P6Off.PreCauchyBounds
import Erdos821.S56.RoughFree

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P6Off

set_option maxHeartbeats 1800000 in
theorem PreCauchyApproximationTask_proof : PreCauchyApproximationTask := by
  intro hsplit hc D hD psi hpsi hsupp a f ha ham harep hf hfm hfrep
  obtain ⟨Cs, hCs, halloc⟩ := smooth_allocation D hD
  obtain ⟨Cm, Km, hCm, hKm, hmass⟩ := weighted_pair_mass_polylog hc D hD
  let Mf := ∫ t, ‖f t‖
  have hMf : 0 ≤ Mf := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨Cs, hCs, ?_⟩
  intro b C0 hb hC0 jstar heta A K0 hA hK0
  let S := A+Cm+2*C0
  obtain ⟨Ka, hKa, hbranch⟩ := branch_truncation_polylog D hD (argumentRadius D) a ha harep ham S
  obtain ⟨Kf, hKf, hcut⟩ := cutoff_truncation_polylog psi f hf hfm hfrep S
  let K := Km*(Kf+Mf*Ka)+2*Mf+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hdata := hD
  obtain ⟨_, _, _, _, _, _, _, _, cmin, cmax, hcmin, hcmax, hvalid⟩ := hdata
  have hsig : 0 < b/4 := by positivity
  filter_upwards [halloc b hb jstar heta K0 hK0.le, hmass jstar,
    hbranch, hcut, discarded_mass_saving hc D hD (b/4) 2 (2*C0) A hsig,
    eventually_exceptional_present D hD jstar, hvalid,
    eventually_rough_groupFree D.geometry,
    eventually_ge_atTop 5, tendsto_L.eventually (eventually_ge_atTop 1)]
    with x halloc hm hbranch hcut htail hj hvalid hfree hx hL
  intro U V alpha beta hUVlo hUVhi hUlo hUhi hVlo hVhi hab hrough
  have hxpos : 0 < x := by linarith
  have hLp : 0 < L x := zero_lt_one.trans_le hL
  have hUpos : 0 < U := (Real.rpow_pos_of_pos hxpos b).trans_le hUlo
  have hVpos : 0 < V := (Real.rpow_pos_of_pos hxpos b).trans_le hVlo
  have hx1 : 1 ≤ x := by linarith
  have hxb : 1 ≤ x^b := Real.one_le_rpow hx1 hb.le
  have hU1 : 1 ≤ U := hxb.trans hUlo
  have hV1 : 1 ≤ V := hxb.trans hVlo
  let E := U*L x^(-K0)
  let emin := E*L x^(-Cs)
  have hE : 0 < E := mul_pos hUpos (Real.rpow_pos_of_pos hLp _)
  have hemin : 0 < emin := mul_pos hE (Real.rpow_pos_of_pos hLp _)
  have hepos : ∀ e ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊, 0 < e := by
    intro e he
    have hge := Nat.ceil_le.mp (Finset.mem_Icc.mp he).1
    have hcast : (0:ℝ) < e := hemin.trans_le hge
    exact_mod_cast hcast
  have hgood (u : ℕ) (hu : x ≤ (u:ℝ))
      (hgp : (groupPart (D.groups x) u : ℝ) ≤ x^(b/4)) :
      allocatedWeight D x jstar emin E u = D.weight x jstar u := by
    apply allocatedWeight_eq_of_partition
    intro z hz
    obtain ⟨hp, hr⟩ := halloc U u z hUlo hUhi hu hz hgp
    exact allocationMass_eq_one D z emin E hE.le hp hr
  let F := fun u : ℕ => (allocatedWeight D x jstar emin E u*psi ((u:ℝ)/x) : ℂ)
  let H := fun u : ℕ => truncatedAllocatedWeight D x jstar emin E a u*truncatedCutoff f (L x) x u
  let eps := (Kf+Mf*Ka)*L x^(-S)
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hM : 0 ≤ L x^C0 := Real.rpow_nonneg hLp.le _
  have hpoint (u : ℕ) (hu : 0 < u) : ‖F u-H u‖ ≤ eps*D.weight x jstar u := by
    have hea : 0 ≤ Ka*L x^(-S) := by positivity
    have hef : 0 ≤ Kf*L x^(-S) := by positivity
    have hae := allocatedWeight_truncation_error D x jstar emin E (Ka*L x^(-S)) a u
      (fun z => allocationMass_truncation_error D z emin E _ a
        (hbranch jstar (Real.log E) (processedLog D z) (processedScale D x jstar)))
    have hfmass : ‖truncatedCutoff f (L x) x u‖ ≤ Mf :=
      fourier_truncated_norm_le_mass f hf (L x) (Real.log (u:ℝ)-Real.log x)
    have hbnd := allocated_cutoff_error D x jstar emin E (Ka*L x^(-S)) (Kf*L x^(-S)) Mf
      a f psi u hea hef hMf hae (hcut u hu) hfmass
    simp only [Complex.ofReal_mul] at hbnd
    apply hbnd.trans_eq
    dsimp [eps]
    ring
  have htrunc := pairSum_weighted_stability D x jstar U V eps (L x^C0) F H alpha beta
    heps hM hpoint (fun n => (hab n).1) (fun n => (hab n).2)
  have htruncfinal : ‖pairSum U V F alpha beta-pairSum U V H alpha beta‖ ≤
      Km*(Kf+Mf*Ka)*x*L x^(-A) := by
    apply htrunc.trans
    calc
      _ ≤ eps*(L x^C0)^2*(Km*x*L x^Cm) :=
        mul_le_mul_of_nonneg_left (hm U V hU1 hV1 hUVhi) (by positivity)
      _ = _ := by
        dsimp [eps]
        rw [pow_two]
        calc
          _ = Km*(Kf+Mf*Ka)*x*(L x^(-S)*L x^C0*L x^C0*L x^Cm) := by ring
          _ = _ := by
            rw [← Real.rpow_add hLp, ← Real.rpow_add hLp, ← Real.rpow_add hLp]
            congr 1
            congr 1
            dsimp [S]
            ring
  have horig : typeIISum D x jstar U V psi alpha beta =
      pairSum U V (fun u => (D.weight x jstar u*psi ((u:ℝ)/x) : ℂ)) alpha beta := by
    simp only [typeIISum, pairSum, dyad, Complex.ofReal_mul]
  have hdiscard := pairSum_allocation_tail_bound D x jstar emin E U V (b/4) (L x^C0) Mf
    psi alpha beta hx hM hMf hsupp (fun y hy => cutoff_norm_le_mass psi f hf hfrep y hy)
    hgood (fun n => (hab n).1) (fun n => (hab n).2) hrough
  simp only [Complex.ofReal_mul] at hdiscard
  have hdiscardfinal : ‖typeIISum D x jstar U V psi alpha beta-pairSum U V F alpha beta‖ ≤
      2*Mf*x*L x^(-A) := by
    rw [horig]
    apply hdiscard.trans
    have hpow : (L x^C0)^2 = L x^(2*C0) := by
      rw [pow_two, ← Real.rpow_add hLp]
      congr 1
      ring
    rw [hpow]
    calc
      _ = Mf*(L x^(2*C0)*Real.exp (2*Real.sqrt (L x))*
          ∑ u ∈ Finset.Icc 1 ⌊2*x⌋₊,
            if x^(b/4) < (groupPart (D.groups x) u : ℝ) then D.weight x jstar u else 0) := by ring
      _ ≤ Mf*((⌊2*x⌋₊:ℝ)*L x^(-A)) := mul_le_mul_of_nonneg_left (htail jstar ⌊2*x⌋₊) hMf
      _ ≤ Mf*(2*x*L x^(-A)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)) hMf
      _ = _ := by ring
  have hexact := preCauchyExpansion_eq_pairSum hsplit D x jstar Cs K0 U V a f alpha beta ha hf
    hj hD.1 hvalid.2.2.2.2 (hfree (D.groups x) hvalid.1) hepos
  rw [hexact]
  apply (norm_sub_le_norm_sub_add_norm_sub (typeIISum D x jstar U V psi alpha beta)
    (pairSum U V F alpha beta) (pairSum U V H alpha beta)).trans
  apply (add_le_add hdiscardfinal htruncfinal).trans
  dsimp [K]
  have hxL : 0 ≤ x*L x^(-A) := by positivity
  nlinarith


end Erdos821.S56Core
