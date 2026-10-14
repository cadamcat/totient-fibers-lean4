import Erdos821.S10.Tasks

noncomputable section
open Filter
namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.P10

/-- Exact extraction boundary after supplying the four remaining contracts. -/
theorem prime_extraction_of_tasks
    (hPresieve : SharpPresieveTask) (hMesh : UnbalancedMeshTask)
    (hCoverage : CompositeCoverageTask) (hBalanced : BalancedCompositeTask) :
    Erdos821.Blueprint.prime_extraction_statement := by
  intro hc hs hII hp δ C hGeometry hBounds hTypeI hBal
  have hSeries : 0 < singularSeries := hp.products.1
  obtain ⟨Kbal, hKbal, hBalancedBound⟩ :=
    hBalanced hc hII hp δ C hGeometry hBounds hBal
  obtain ⟨κ, hκ, hκsmall, hκsaving⟩ := choose_kappa singularSeries Kbal hSeries hKbal
  obtain ⟨b, hb, hbκ, hPresieveBound⟩ :=
    hPresieve hc hs hp δ C hGeometry hBounds hTypeI κ (singularSeries / 16)
      hκ (by positivity)
  obtain ⟨jstar, hjstar, hLate⟩ := exists_late_slot C δ b hGeometry hb
  have hslot : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < b / 12 := by
    rw [hGeometry.2.2.2.1]
    simpa [div_eq_mul_inv, one_div_pow] using hLate
  obtain ⟨N, hN, hMeshBound⟩ :=
    hMesh hc hs hII hp δ C hGeometry hBounds hTypeI b κ (1 / 16)
      hb hbκ hκ hκsmall (by norm_num) jstar hjstar hslot
  have hCoverageBound := hCoverage δ C hBounds b κ hb hbκ hκ hκsmall N hN jstar hjstar
  have hbstar : 0 < b / 3 := by positivity
  have hbstarSmall : b / 3 < 1 / 10 := by linarith
  have hslot' : C.bands.c₂ * C.bands.s' / C.bands.ratio ^ jstar < (b / 3) / 4 := by
    convert hslot using 1 <;> ring
  have hBalancedEvent := hBalancedBound κ (b / 3) hκ hκsmall hbstar hbstarSmall
    jstar hjstar hslot' (singularSeries / 16) (by positivity)
  rcases hBounds with ⟨Kcand, CA, cmin, cmax, hKcand, hcmin, hcmax, hBound⟩
  refine ⟨jstar, hjstar, singularSeries / 2, by positivity, ?_⟩
  filter_upwards [hPresieveBound jstar hjstar, hMeshBound, hCoverageBound,
    hBalancedEvent, hBound jstar hjstar, eventually_gt_atTop (1 : ℝ)]
    with x hP hU hC hB hData hx
  have hL : 0 < Analytic.L x := Real.log_pos hx
  have hMass : 0 ≤ C.mass x jstar :=
    le_trans (mul_nonneg (by linarith) (Real.rpow_nonneg hL.le _)) hData.1
  have hScale : 0 ≤ C.mass x jstar / Analytic.L x := div_nonneg hMass hL.le
  have hκscaled : Kbal * κ * (C.mass x jstar / Analytic.L x) ≤
      singularSeries / 4 * (C.mass x jstar / Analytic.L x) :=
    mul_le_mul_of_nonneg_right hκsaving.le hScale
  have hCombined :
      (singularSeries * roughDensity b 1 - singularSeries / 16) *
        (C.mass x jstar / Analytic.L x) ≤
      C.primeMass x jstar +
        singularSeries * (roughDensity b 1 - 1 + 1 / 16) *
          (C.mass x jstar / Analytic.L x) +
        (Kbal * κ + singularSeries / 16) * (C.mass x jstar / Analytic.L x) := by
    calc
      _ ≤ candidateSiftedMass C x jstar (x ^ b) := by simpa [mul_div_assoc] using hP
      _ ≤ C.primeMass x jstar + unbalancedMeshMass C x jstar b κ N +
          balancedCompositeMass C x jstar κ := hC
      _ ≤ _ := by
        simpa [mul_div_assoc] using add_le_add (add_le_add (le_refl (C.primeMass x jstar)) hU) hB
  have hRemaining : singularSeries / 2 * (C.mass x jstar / Analytic.L x) ≤
      C.primeMass x jstar := by
    nlinarith [mul_nonneg hSeries.le hScale]
  simpa [mul_div_assoc] using hRemaining

example (hPresieve : SharpPresieveTask) (hMesh : UnbalancedMeshTask)
    (hCoverage : CompositeCoverageTask) (hBalanced : BalancedCompositeTask) :
    Erdos821.Blueprint.prime_extraction_statement :=
  prime_extraction_of_tasks hPresieve hMesh hCoverage hBalanced

end Erdos821.P7Core
