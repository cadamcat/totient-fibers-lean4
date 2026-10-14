import Erdos821.P8Grid.Base

noncomputable section
open scoped BigOperators
open Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Grid
open Blueprint Blueprint.Analytic

/-- For one length `l`, every active tail tuple lies in an interior box of the
inflated simplex with parameters `(gamma - h, w + d + (K + 1) h)`, and its kernel is
dominated by that box's kernel up to the factor `1 + a`. -/
theorem tailPrimeGridTerm_le_grid {x S gamma w eta b h tau d D : ℝ} {P : Finset ℕ}
    {l N K : ℕ} (hx : 1 < x) (hb : 0 < b) (hbg : b ≤ gamma) (hgw : gamma < w)
    (hd : d = L x ^ (-S) / L x) (hd0 : 0 ≤ d) (hdb : d ≤ b / 2)
    (hh : 0 < h) (hhb : h ≤ b / 2) (heta : 0 ≤ eta) (htau : 0 ≤ tau)
    (hl : 2 ≤ l) (hlK : l - 1 ≤ K)
    (hcover : w ≤ b / 2 + (N : ℝ) * h)
    (hD : (∑ j : Fin N, simplexGridCellLogWidth (b / 2) h j.val) = D)
    (hP : ∀ p ∈ P, p.Prime ∧ x ^ gamma < (p : ℝ))
    (hmass : ∀ j : Fin N, simplexGridCellMass x (b / 2) h P j.val ≤
      simplexGridCellLogWidth (b / 2) h j.val + tau) :
    tailPrimeGridTerm x S w eta P l ≤
      (1 + 2 * (d + (2 * (K : ℝ) + 1) * h) / b + eta * (w + d + ((K : ℝ) + 1) * h)) *
        (densityTerm (gamma - h) (w + d + ((K : ℝ) + 1) * h) l +
          (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) * D ^ (l - 1) +
          (b / 2)⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1))) := by
  classical
  have hx0 : 0 < x := by linarith
  have hL : 0 < Analytic.L x := by simpa [Analytic.L] using Real.log_pos hx
  have hgamma0 : 0 < gamma := hb.trans_le hbg
  have hb0 : 0 < b / 2 := by positivity
  have hw0 : 0 < w := hgamma0.trans hgw
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set gamma' := gamma - h with hgamma'
  set w' := w + d + ((K : ℝ) + 1) * h with hw'
  set A := 1 + 2 * (d + (2 * (K : ℝ) + 1) * h) / b +
    eta * (w + d + ((K : ℝ) + 1) * h) with hA
  have hbg' : b / 2 ≤ gamma' := by rw [hgamma']; linarith
  have hgamma'0 : 0 < gamma' := hb0.trans_le hbg'
  have hgw' : gamma' < w' := by
    rw [hgamma', hw']
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (K : ℝ) + 1) hh.le]
  have hA0 : 0 ≤ A := by
    rw [hA]
    have h1 : 0 ≤ 2 * (d + (2 * (K : ℝ) + 1) * h) / b := by positivity
    have h2 : 0 ≤ eta * (w + d + ((K : ℝ) + 1) * h) := by positivity
    linarith
  let J : Finset (Fin (l - 1) → Fin N) :=
    Finset.univ.filter fun v => simplexGridInterior gamma' w' (b / 2) h v
  let G : (Fin (l - 1) → Fin N) → ℝ := fun v =>
    (w' - ∑ i, simplexGridUpper (b / 2) h v i)⁻¹
  have hJmem : ∀ v, v ∈ J ↔ simplexGridInterior gamma' w' (b / 2) h v := by
    intro v
    simp [J]
  have hGpos : ∀ v ∈ J, 0 < w' - ∑ i, simplexGridUpper (b / 2) h v i := by
    intro v hv
    have hint := (hJmem v).mp hv
    linarith [hint.2]
  have hG : ∀ v ∈ J, 0 ≤ G v := fun v hv => inv_nonneg.mpr (hGpos v hv).le
  have hboxTerm_nonneg : ∀ (v : Fin (l - 1) → Fin N) (f : Fin (l - 1) → PrimeLabel P),
      0 ≤ (if simplexGridPrimeBox x (b / 2) h P v f then
        (tupleTailProduct f : ℝ)⁻¹ else 0) := by
    intro v f
    split_ifs
    · positivity
    · exact le_rfl
  have hpoint : ∀ f : Fin (l - 1) → PrimeLabel P,
      (if (roughLogCellLastChoices x S w P f).Nonempty then
        ((Real.log (x ^ w / (tupleTailProduct f : ℝ)) / L x)⁻¹ + eta) /
          (tupleTailProduct f : ℝ) else 0) ≤
      A * ∑ v ∈ J, G v *
        (if simplexGridPrimeBox x (b / 2) h P v f then
          (tupleTailProduct f : ℝ)⁻¹ else 0) := by
    intro f
    have hRHS : 0 ≤ A * ∑ v ∈ J, G v *
        (if simplexGridPrimeBox x (b / 2) h P v f then
          (tupleTailProduct f : ℝ)⁻¹ else 0) :=
      mul_nonneg hA0 (Finset.sum_nonneg fun v hv =>
        mul_nonneg (hG v hv) (hboxTerm_nonneg v f))
    by_cases hne : (roughLogCellLastChoices x S w P f).Nonempty
    · rw [if_pos hne]
      obtain ⟨hcoord, hsumU⟩ :=
        roughLogCellLastChoices_exponent_support hx hL P hP f hne
      let u : Fin (l - 1) → ℝ := fun i => primeLogCoordinate x (f i).val
      have hu_gamma : ∀ i, gamma ≤ u i := fun i => (hcoord i).le
      have hu_sum : (∑ i, u i) ≤ w + d - gamma := by
        have h' : (∑ i, u i) ≤ w - gamma + L x ^ (-S) / Analytic.L x := hsumU
        rw [hd]
        exact h'.trans_eq (by ring)
      have hu_le : ∀ i, u i ≤ w := by
        intro i
        have hsingle : u i ≤ ∑ i', u i' :=
          Finset.single_le_sum (fun i' _ => hgamma0.le.trans (hu_gamma i'))
            (Finset.mem_univ i)
        linarith
      -- every label lies in one cell of the exponent grid
      have hcell : ∀ i, ∃ j < N, (f i).val ∈ exponentGridCell x (b / 2) h j := by
        intro i
        have hprime := (hP (f i).val (f i).property).1
        have hpx : x ^ u i = ((f i).val : ℝ) := primeLogCoordinate_rpow hx hprime
        have hmem : (f i).val ∈ Finset.Ioc (exponentGridEndpoint x (b / 2) h 0)
            (exponentGridEndpoint x (b / 2) h N) := by
          rw [Finset.mem_Ioc]
          constructor
          · unfold exponentGridEndpoint
            apply (Nat.floor_lt (by positivity)).2
            calc x ^ (b / 2 + ((0 : ℕ) : ℝ) * h) ≤ x ^ gamma := by
                  apply Real.rpow_le_rpow_of_exponent_le hx.le
                  simp
                  linarith
              _ < ((f i).val : ℝ) := (hP (f i).val (f i).property).2
          · unfold exponentGridEndpoint
            apply Nat.le_floor
            rw [← hpx]
            apply Real.rpow_le_rpow_of_exponent_le hx.le
            linarith [hu_le i]
        rw [← exponentGridCell_union_range x (b / 2) h N hx hh.le] at hmem
        obtain ⟨j, hj, hjcell⟩ := Finset.mem_biUnion.mp hmem
        exact ⟨j, Finset.mem_range.mp hj, hjcell⟩
      choose j hjN hjcell using hcell
      let v : Fin (l - 1) → Fin N := fun i => ⟨j i, hjN i⟩
      have hboxi : ∀ i, (f i).val ∈
          (Finset.Ioc ⌊x ^ (simplexGridLower (b / 2) h v i)⌋₊
            ⌊x ^ (simplexGridUpper (b / 2) h v i)⌋₊).filter Nat.Prime := by
        intro i
        have hc := hjcell i
        unfold exponentGridCell exponentGridEndpoint at hc
        have hup : b / 2 + ((j i + 1 : ℕ) : ℝ) * h = simplexGridUpper (b / 2) h v i := by
          simp only [simplexGridUpper, simplexGridLower, v, Nat.cast_add, Nat.cast_one]
          ring
        have hlo : b / 2 + ((j i : ℕ) : ℝ) * h = simplexGridLower (b / 2) h v i := by
          simp only [simplexGridLower, v]
        rw [hup, hlo] at hc
        exact Finset.mem_filter.mpr ⟨hc, (hP (f i).val (f i).property).1⟩
      have hbox : simplexGridPrimeBox x (b / 2) h P v f := hboxi
      have hcoordBox : ∀ i, simplexGridLower (b / 2) h v i < u i ∧
          u i ≤ simplexGridUpper (b / 2) h v i := fun i =>
        primeInterval_mem_logCoordinate hx (hP (f i).val (f i).property).1 (hboxi i)
      let a : Fin (l - 1) → ℝ := fun i => simplexGridLower (b / 2) h v i
      have hae : ∀ i, a i ≤ u i := fun i => (hcoordBox i).1.le
      have hea : ∀ i, u i ≤ a i + h := fun i => (hcoordBox i).2
      have hcardK : Fintype.card (Fin (l - 1)) ≤ K := by simpa using hlK
      have hkernel := P8Core.rounded_box_kernel_inflation (b := b) (gamma := gamma)
        (w := w) (d := d) (h := h) (eta := eta) (K := K) a u hb hbg hd0 hdb hh.le hhb heta
        hcardK hae hea hu_gamma hu_sum
      have hinside := P8Core.rounded_box_inside_inflated_simplex (gamma := gamma)
        (w := w) (d := d) (h := h) (K := K) a u hh.le hcardK hae hea hu_gamma hu_sum
      have hvJ : v ∈ J := by
        rw [hJmem]
        refine ⟨fun i => ?_, ?_⟩
        · rw [hgamma']
          exact hinside.1 i
        · have h2 := hinside.2
          have hsumEq : (∑ i, simplexGridUpper (b / 2) h v i) = ∑ i, (a i + h) := by
            simp [a, simplexGridUpper]
          rw [hsumEq, hw', hgamma']
          linarith
      have hlowUp : (w' - ∑ i, a i)⁻¹ ≤ G v := by
        have hpos := hGpos v hvJ
        have hle : (∑ i, a i) ≤ ∑ i, simplexGridUpper (b / 2) h v i :=
          Finset.sum_le_sum fun i _ => by simp [a, simplexGridUpper, hh.le]
        exact inv_anti₀ hpos (by linarith)
      have hresid : (Real.log (x ^ w / (tupleTailProduct f : ℝ)) / L x) =
          w - ∑ i, u i :=
        tailTupleResidual_eq hx (fun p hp => (hP p hp).1) f
      have hQpos : 0 < (tupleTailProduct f : ℝ) := by
        rw [tupleTailProduct_eq_rpow_sum hx (fun p hp => (hP p hp).1) f]
        exact Real.rpow_pos_of_pos hx0 _
      have hsingle : G v * (if simplexGridPrimeBox x (b / 2) h P v f then
            (tupleTailProduct f : ℝ)⁻¹ else 0) ≤
          ∑ v' ∈ J, G v' * (if simplexGridPrimeBox x (b / 2) h P v' f then
            (tupleTailProduct f : ℝ)⁻¹ else 0) :=
        Finset.single_le_sum (f := fun v' => G v' *
            (if simplexGridPrimeBox x (b / 2) h P v' f then
              (tupleTailProduct f : ℝ)⁻¹ else 0))
          (fun v' hv' => mul_nonneg (hG v' hv') (hboxTerm_nonneg v' f)) hvJ
      rw [if_pos hbox] at hsingle
      rw [hresid, div_eq_mul_inv]
      have hk' : (w - ∑ i, u i)⁻¹ + eta ≤ A * G v := by
        have hk2 : (w - ∑ i, u i)⁻¹ + eta ≤ A * (w' - ∑ i, a i)⁻¹ := by
          rw [hA, hw']
          exact hkernel
        exact hk2.trans (mul_le_mul_of_nonneg_left hlowUp hA0)
      calc ((w - ∑ i, u i)⁻¹ + eta) * (tupleTailProduct f : ℝ)⁻¹ ≤
            (A * G v) * (tupleTailProduct f : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hk' (inv_nonneg.mpr hQpos.le)
        _ = A * (G v * (tupleTailProduct f : ℝ)⁻¹) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsingle hA0
    · rw [if_neg hne]
      exact hRHS
  have hsum : tailPrimeGridTerm x S w eta P l ≤
      A * ∑ v ∈ J, G v * ∏ i, simplexGridCellMass x (b / 2) h P (v i).val := by
    unfold tailPrimeGridTerm
    calc _ ≤ ∑ f : Fin (l - 1) → PrimeLabel P, A * ∑ v ∈ J, G v *
          (if simplexGridPrimeBox x (b / 2) h P v f then
            (tupleTailProduct f : ℝ)⁻¹ else 0) :=
          Finset.sum_le_sum fun f _ => hpoint f
      _ = A * ∑ v ∈ J, G v * ∑ f : Fin (l - 1) → PrimeLabel P,
          (if simplexGridPrimeBox x (b / 2) h P v f then
            (tupleTailProduct f : ℝ)⁻¹ else 0) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.mul_sum]
      _ = A * ∑ v ∈ J, G v * ∏ i, simplexGridCellMass x (b / 2) h P (v i).val := by
          congr 1
          apply Finset.sum_congr rfl
          intro v _
          rw [simplexGridPrimeBox_mass_eq x (b / 2) h P v]
  have hgrid := simplexGridInterior_primeMass_le (x := x) (gamma := gamma') (w := w')
    (b := b / 2) (h := h) (tau := tau) (D := D) (P := P) (l := l) (N := N)
    hl hgamma'0 hgw' hb0 hbg' hh.le htau hD hmass J
    (fun v hv => (hJmem v).mp hv)
    (fun v _ v' _ hne => simplexGridBox_disjoint hh.le hne)
  exact hsum.trans (mul_le_mul_of_nonneg_left hgrid hA0)

/-- A linear quantity in a small positive parameter is eventually below any positive bound. -/
theorem eventually_mul_lt_nhdsGT (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), c * h < r := by
  have h1 : Tendsto (fun h : ℝ => c * h) (𝓝 0) (𝓝 0) := by
    have h2 := (tendsto_const_nhds (x := c) (f := 𝓝 (0 : ℝ))).mul
      (tendsto_id (x := 𝓝 (0 : ℝ)))
    simpa using h2
  exact (h1.eventually (gt_mem_nhds hr)).filter_mono nhdsWithin_le_nhds

/-- The cell-width parameter `L x ^ (-S) / L x` tends to zero from above. -/
theorem eventually_cellWidth_le {S r : ℝ} (hS : 0 < S) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ 0 ≤ L x ^ (-S) / L x ∧ L x ^ (-S) / L x < r := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop (max 1 r⁻¹)] with x hx hlog
  have hL1 : 1 ≤ L x := by
    have : (1 : ℝ) ≤ Real.log x := (le_max_left _ _).trans hlog.le
    simpa [Analytic.L] using this
  have hLr : r⁻¹ < L x := by
    have : r⁻¹ < Real.log x := (le_max_right _ _).trans_lt hlog
    simpa [Analytic.L] using this
  have hL0 : 0 < L x := by linarith
  have hpow0 : 0 ≤ L x ^ (-S) := Real.rpow_nonneg hL0.le _
  have hpow1 : L x ^ (-S) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  refine ⟨hx, div_nonneg hpow0 hL0.le, ?_⟩
  calc L x ^ (-S) / L x ≤ 1 / L x := div_le_div_of_nonneg_right hpow1 hL0.le
    _ < r := by
      rw [div_lt_iff₀ hL0]
      have := (inv_lt_iff_one_lt_mul₀ hr).mp hLr
      linarith

set_option maxHeartbeats 800000 in
/-- Uniform finite-grid upper bound for the weighted tail-prime sums. -/
theorem tailPrimeGridSimplexUpper (hC : ClassicalInputs)
    (b wMax gap S : ℝ) (hb : 0 < b) (hwMax : 0 < wMax)
    (hgap : 0 < gap) (hS : 0 < S) {eps : ℝ} (heps : 0 < eps) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ x : ℝ in atTop, ∀ gamma w : ℝ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ x ^ gamma < (p : ℝ)) →
        tailPrimeGridMass x S w eta P ⌊wMax / b⌋₊ ≤
          (∑ l ∈ Finset.Icc 2 ⌊wMax / b⌋₊,
            densityTerm gamma w l / (l.factorial : ℝ)) + eps := by
  obtain ⟨rho, hrho, hgrid⟩ := P8Core.densityTerm_sum_grid_errors (wMax := wMax) hb hgap heps
  set K := ⌊wMax / b⌋₊ with hKdef
  set R := min rho 1 with hRdef
  have hR0 : 0 < R := lt_min hrho one_pos
  have hRrho : R ≤ rho := min_le_left _ _
  have hR1 : R ≤ 1 := min_le_right _ _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hb0 : 0 < b / 2 := by positivity
  set Dm := (wMax + 1) / (b / 2) with hDm
  have hDm0 : 0 ≤ Dm := by positivity
  -- the mesh
  set c1 := (K : ℝ) / (b / 2) ^ 2 * (1 + Dm) ^ K with hc1
  have hevh : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h < 1 ∧ h < b / 2 ∧
      ((K : ℝ) + 1) * h < R / 2 ∧ (2 * (2 * (K : ℝ) + 1) / b) * h < R / 4 ∧
      (2 * (K : ℝ) * c1) * h < R / 2 := by
    filter_upwards [eventually_mul_lt_nhdsGT 1 one_pos, eventually_mul_lt_nhdsGT 1 hb0,
      eventually_mul_lt_nhdsGT ((K : ℝ) + 1) (show 0 < R / 2 by positivity),
      eventually_mul_lt_nhdsGT (2 * (2 * (K : ℝ) + 1) / b) (show 0 < R / 4 by positivity),
      eventually_mul_lt_nhdsGT (2 * (K : ℝ) * c1) (show 0 < R / 2 by positivity),
      eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with h h1 h2 h3 h4 h5 h6
    exact ⟨h6, by simpa using h1, by simpa using h2, h3, h4, h5⟩
  obtain ⟨h, hh0', hh1, hhb, hhK, hhA, hhE⟩ := hevh.exists
  -- the small weight
  have heveta : ∀ᶠ eta in 𝓝[>] (0 : ℝ), 0 < eta ∧ (wMax + 2) * eta < R / 4 := by
    filter_upwards [eventually_mul_lt_nhdsGT (wMax + 2) (show 0 < R / 4 by positivity),
      eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with eta h1 h2
    exact ⟨h2, h1⟩
  obtain ⟨eta, heta0', heta⟩ := heveta.exists
  refine ⟨eta, heta0', ?_⟩
  -- the grid
  set N := ⌈wMax / h⌉₊ with hNdef
  have hNh : wMax ≤ (N : ℝ) * h := by
    have := Nat.le_ceil (wMax / h)
    rw [div_le_iff₀ hh0'] at this
    exact this
  have hNh' : (N : ℝ) * h ≤ wMax + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ wMax / h by positivity)
    have h2 : (N : ℝ) < wMax / h + 1 := this
    have h3 := mul_lt_mul_of_pos_right h2 hh0'
    rw [add_mul, div_mul_cancel₀ _ hh0'.ne', one_mul] at h3
    linarith
  set D := ∑ j : Fin N, simplexGridCellLogWidth (b / 2) h j.val with hDdef
  have hD0 : 0 ≤ D := by
    apply Finset.sum_nonneg
    intro j _
    have hb' := simplexGridCellLogWidth_bounds (W := b / 2 + ((j.val + 1 : ℕ) : ℝ) * h)
      hb0 hh0' j.val le_rfl
    have : 0 ≤ h / (b / 2 + ((j.val + 1 : ℕ) : ℝ) * h) := by positivity
    linarith [hb'.1]
  have hDDm : D ≤ Dm := by
    have hcell : ∀ j : Fin N, simplexGridCellLogWidth (b / 2) h j.val ≤ h / (b / 2) := by
      intro j
      exact (simplexGridCellLogWidth_bounds (W := b / 2 + ((j.val + 1 : ℕ) : ℝ) * h)
        hb0 hh0' j.val le_rfl).2
    calc D ≤ ∑ _j : Fin N, h / (b / 2) := Finset.sum_le_sum fun j _ => hcell j
      _ = (N : ℝ) * h / (b / 2) := by simp; ring
      _ ≤ Dm := by rw [hDm]; exact div_le_div_of_nonneg_right hNh' hb0.le
  -- the prime-mass tolerance
  set c2 := (b / 2)⁻¹ * ((K : ℝ) * (N : ℝ) * (2 + Dm) ^ K) with hc2
  have hevtau : ∀ᶠ tau in 𝓝[>] (0 : ℝ), 0 < tau ∧ (N : ℝ) * tau < 1 ∧
      (2 * (K : ℝ) * c2) * tau < R / 2 := by
    filter_upwards [eventually_mul_lt_nhdsGT (N : ℝ) one_pos,
      eventually_mul_lt_nhdsGT (2 * (K : ℝ) * c2) (show 0 < R / 2 by positivity),
      eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with tau h1 h2 h3
    exact ⟨h3, h1, h2⟩
  obtain ⟨tau, htau0', htauN, htauE⟩ := hevtau.exists
  have hdmin : 0 < min (b / 2) (min 1 (min (R / 2) (b * R / 8))) := by
    apply lt_min hb0 (lt_min one_pos (lt_min (by positivity) (by positivity)))
  filter_upwards [eventually_cellWidth_le hS hdmin,
    simplexGridCellMass_uniform_log_upper hb0 hh0'.le htau0'] with x hxd hcell
  obtain ⟨hx, hd0, hdlt⟩ := hxd
  set d := L x ^ (-S) / L x with hddef
  have hdb : d ≤ b / 2 := (hdlt.trans_le (min_le_left _ _)).le
  have hd1 : d ≤ 1 := (hdlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hdR : d < R / 2 := hdlt.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdbR : d < b * R / 8 := hdlt.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  intro gamma w hbg hgw hww P hP
  have hgamma0 : 0 < gamma := hb.trans_le hbg
  have hgw' : gamma < w := by linarith
  set A := 1 + 2 * (d + (2 * (K : ℝ) + 1) * h) / b +
    eta * (w + d + ((K : ℝ) + 1) * h) with hA
  set a := A - 1 with ha
  have hKh : ((K : ℝ) + 1) * h < R / 2 := hhK
  have hKh1 : ((K : ℝ) + 1) * h ≤ 1 := by linarith
  have ha0 : 0 ≤ a := by
    rw [ha, hA]
    have h1 : 0 ≤ 2 * (d + (2 * (K : ℝ) + 1) * h) / b := by positivity
    have h2 : 0 ≤ eta * (w + d + ((K : ℝ) + 1) * h) := by
      apply mul_nonneg heta0'.le
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (K : ℝ) + 1) hh0'.le]
    linarith
  have haR : a < R := by
    have h1 : 2 * (d + (2 * (K : ℝ) + 1) * h) / b =
        2 * d / b + (2 * (2 * (K : ℝ) + 1) / b) * h := by ring
    have h2 : 2 * d / b < R / 4 := by
      rw [div_lt_iff₀ hb]; linarith
    have h3 : eta * (w + d + ((K : ℝ) + 1) * h) ≤ eta * (wMax + 2) := by
      apply mul_le_mul_of_nonneg_left _ heta0'.le
      linarith
    rw [ha, hA, h1]
    linarith
  have hA2 : A ≤ 2 := by
    have : a < 1 := haR.trans_le hR1
    rw [ha] at this
    linarith
  have hA0 : 0 ≤ A := by rw [ha] at ha0; linarith
  -- the per-length error
  let e : ℕ → ℝ := fun l => (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) * D ^ (l - 1) +
    (b / 2)⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1))
  have hgh : b / 2 ≤ gamma - h := by linarith
  have hgh0 : 0 < gamma - h := hb0.trans_le hgh
  have he_bound : ∀ l ∈ Finset.Icc 2 K, 0 ≤ e l ∧ e l ≤ c1 * h + c2 * tau := by
    intro l hl
    have hlK : l - 1 ≤ K := by have := (Finset.mem_Icc.mp hl).2; omega
    have hlK' : ((l - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hlK
    have hNtau0 : 0 ≤ (N : ℝ) * tau := by positivity
    have hNtau1 : (N : ℝ) * tau ≤ 1 := htauN.le
    have hDpow : D ^ (l - 1) ≤ (1 + Dm) ^ K :=
      (pow_le_pow_left₀ hD0 (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) hlK)
    have hdiff := pow_add_diff_le hD0 hNtau0 (l - 1)
    have hpow2 : (1 + D + (N : ℝ) * tau) ^ (l - 1) ≤ (2 + Dm) ^ K :=
      (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) hlK)
    have hdiff0 : 0 ≤ (D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1) :=
      sub_nonneg.mpr (pow_le_pow_left₀ hD0 (by linarith) _)
    have he1 : (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) * D ^ (l - 1) ≤ c1 * h := by
      have hsq : (b / 2) ^ 2 ≤ (gamma - h) ^ 2 := pow_le_pow_left₀ hb0.le hgh 2
      have : (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) ≤ (K : ℝ) * h / (b / 2) ^ 2 := by
        gcongr
      calc (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) * D ^ (l - 1) ≤
            ((K : ℝ) * h / (b / 2) ^ 2) * (1 + Dm) ^ K := by
            apply mul_le_mul this hDpow (by positivity) (by positivity)
        _ = c1 * h := by rw [hc1]; ring
    have he2 : (b / 2)⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1)) ≤ c2 * tau := by
      have : (D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1) ≤
          (K : ℝ) * ((N : ℝ) * tau) * (2 + Dm) ^ K := by
        calc _ ≤ ((l - 1 : ℕ) : ℝ) * ((N : ℝ) * tau) * (1 + D + (N : ℝ) * tau) ^ (l - 1) :=
              hdiff
          _ ≤ (K : ℝ) * ((N : ℝ) * tau) * (2 + Dm) ^ K := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hlK' hNtau0) hpow2
                (by positivity) (by positivity)
      calc _ ≤ (b / 2)⁻¹ * ((K : ℝ) * ((N : ℝ) * tau) * (2 + Dm) ^ K) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = c2 * tau := by rw [hc2]; ring
    refine ⟨?_, by linarith⟩
    have : 0 ≤ (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) * D ^ (l - 1) := by positivity
    have : 0 ≤ (b / 2)⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1)) :=
      mul_nonneg (by positivity) hdiff0
    simp only [e]
    linarith
  set w' := w + d + ((K : ℝ) + 1) * h with hw'
  have hterm : ∀ l ∈ Finset.Icc 2 K,
      tailPrimeGridTerm x S w eta P l / (l.factorial : ℝ) ≤
        A * (densityTerm (gamma - h) w' l / (l.factorial : ℝ)) +
          A * e l / (l.factorial : ℝ) := by
    intro l hl
    have hl2 : 2 ≤ l := (Finset.mem_Icc.mp hl).1
    have hlK : l - 1 ≤ K := by have := (Finset.mem_Icc.mp hl).2; omega
    have hbound := tailPrimeGridTerm_le_grid (x := x) (S := S) (gamma := gamma) (w := w)
      (eta := eta) (b := b) (h := h) (tau := tau) (d := d) (D := D) (P := P) (l := l)
      (N := N) (K := K) hx hb hbg hgw' rfl hd0 hdb hh0' hhb.le heta0'.le htau0'.le hl2 hlK
      (by linarith) hDdef.symm hP (fun j => hcell P j.val)
    have hfac : 0 < (l.factorial : ℝ) := by positivity
    have he_l : e l = (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) * D ^ (l - 1) +
        (b / 2)⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1)) := rfl
    have hEq : A * (densityTerm (gamma - h) w' l / (l.factorial : ℝ)) +
          A * e l / (l.factorial : ℝ) =
        ((1 + 2 * (d + (2 * (K : ℝ) + 1) * h) / b +
          eta * (w + d + ((K : ℝ) + 1) * h)) *
          (densityTerm (gamma - h) (w + d + ((K : ℝ) + 1) * h) l +
            (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) * D ^ (l - 1) +
            (b / 2)⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1)))) /
          (l.factorial : ℝ) := by
      rw [hA, hw', he_l]; ring
    have hdiv0 : tailPrimeGridTerm x S w eta P l / (l.factorial : ℝ) ≤
        ((1 + 2 * (d + (2 * (K : ℝ) + 1) * h) / b +
          eta * (w + d + ((K : ℝ) + 1) * h)) *
          (densityTerm (gamma - h) (w + d + ((K : ℝ) + 1) * h) l +
            (((l - 1 : ℕ) : ℝ) * h / (gamma - h) ^ 2) * D ^ (l - 1) +
            (b / 2)⁻¹ * ((D + (N : ℝ) * tau) ^ (l - 1) - D ^ (l - 1)))) /
          (l.factorial : ℝ) :=
      div_le_div_of_nonneg_right hbound hfac.le
    exact hdiv0.trans_eq hEq.symm
  have hEsum : (∑ l ∈ Finset.Icc 2 K, A * e l / (l.factorial : ℝ)) < rho := by
    have hle : ∀ l ∈ Finset.Icc 2 K, A * e l / (l.factorial : ℝ) ≤
        2 * (c1 * h + c2 * tau) := by
      intro l hl
      obtain ⟨he0, he1⟩ := he_bound l hl
      have hfac : (1 : ℝ) ≤ (l.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero l)
      calc A * e l / (l.factorial : ℝ) ≤ A * e l :=
            div_le_self (mul_nonneg hA0 he0) hfac
        _ ≤ 2 * (c1 * h + c2 * tau) :=
            mul_le_mul hA2 he1 he0 (by norm_num)
    have hcard : ((Finset.Icc 2 K).card : ℝ) ≤ K := by
      rw [Nat.card_Icc]
      exact_mod_cast (by omega : K + 1 - 2 ≤ K)
    have hc0 : 0 ≤ 2 * (c1 * h + c2 * tau) := by
      have : 0 ≤ c1 := by rw [hc1]; positivity
      have : 0 ≤ c2 := by rw [hc2]; positivity
      positivity
    calc (∑ l ∈ Finset.Icc 2 K, A * e l / (l.factorial : ℝ)) ≤
          ∑ _l ∈ Finset.Icc 2 K, 2 * (c1 * h + c2 * tau) := Finset.sum_le_sum hle
      _ = ((Finset.Icc 2 K).card : ℝ) * (2 * (c1 * h + c2 * tau)) := by simp
      _ ≤ (K : ℝ) * (2 * (c1 * h + c2 * tau)) := mul_le_mul_of_nonneg_right hcard hc0
      _ = (2 * (K : ℝ) * c1) * h + (2 * (K : ℝ) * c2) * tau := by ring
      _ < R / 2 + R / 2 := add_lt_add hhE htauE
      _ = R := by ring
      _ ≤ rho := hRrho
  have hgamma_close : |(gamma - h) - gamma| < rho := by
    rw [show (gamma - h) - gamma = -h by ring, abs_neg, abs_of_pos hh0']
    have hKh_le : h ≤ ((K : ℝ) + 1) * h := by
      have hKmul : 0 ≤ (K : ℝ) * h := mul_nonneg hK0 hh0'.le
      have : ((K : ℝ) + 1) * h = (K : ℝ) * h + h := by ring
      linarith
    linarith [hhK, hRrho, hR0, hrho, hKh_le]
  have hw_close : |w' - w| < rho := by
    rw [hw', show w + d + ((K : ℝ) + 1) * h - w = d + ((K : ℝ) + 1) * h by ring,
      abs_of_nonneg (by positivity)]
    linarith
  have hfinal := hgrid gamma w (gamma - h) w' a
    (∑ l ∈ Finset.Icc 2 K, A * e l / (l.factorial : ℝ)) K hbg hgw hww le_rfl
    hgamma_close hw_close ha0 (haR.trans_le hRrho) hEsum
  have hAa : 1 + a = A := by rw [ha]; ring
  rw [hAa] at hfinal
  calc tailPrimeGridMass x S w eta P K =
        ∑ l ∈ Finset.Icc 2 K, tailPrimeGridTerm x S w eta P l / (l.factorial : ℝ) := rfl
    _ ≤ ∑ l ∈ Finset.Icc 2 K, (A * (densityTerm (gamma - h) w' l / (l.factorial : ℝ)) +
          A * e l / (l.factorial : ℝ)) := Finset.sum_le_sum hterm
    _ = A * (∑ l ∈ Finset.Icc 2 K, densityTerm (gamma - h) w' l / (l.factorial : ℝ)) +
          ∑ l ∈ Finset.Icc 2 K, A * e l / (l.factorial : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := hfinal

end Erdos821.P8Grid
