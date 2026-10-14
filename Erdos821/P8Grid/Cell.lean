import Erdos821.P8Grid.Grid

noncomputable section
open scoped BigOperators
open Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Grid
open Blueprint Blueprint.Analytic

theorem rpow_short_interval_error_identity {b S L : ℝ}
    (hb : 0 < b) (hL : 0 < L) :
    (b * L) ^ (-(S + 3)) =
      b ^ (-(S + 3)) * L ^ ((-2 : ℝ)) * (L ^ (-S) / L) := by
  rw [Real.mul_rpow hb.le hL.le]
  calc
    b ^ (-(S + 3)) * L ^ (-(S + 3)) =
        b ^ (-(S + 3)) * (L ^ ((-2 : ℝ)) * L ^ (-(S + 1))) := by
          rw [show -(S + 3) = (-2 : ℝ) + (-(S + 1)) by ring, Real.rpow_add hL]
    _ = b ^ (-(S + 3)) * (L ^ ((-2 : ℝ)) * (L ^ (-S) * L ^ ((-1 : ℝ)))) := by
          rw [show -(S + 1) = -S + (-1 : ℝ) by ring, Real.rpow_add hL]
    _ = b ^ (-(S + 3)) * L ^ ((-2 : ℝ)) * (L ^ (-S) / L) := by
          rw [Real.rpow_neg hL.le (1 : ℝ)]
          simp [div_eq_mul_inv]
          ring


set_option maxHeartbeats 600000 in
theorem primeShortCellUpper (hC : ClassicalInputs) {b S eps : ℝ}
    (hb : 0 < b) (hS : 0 < S) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ w : ℝ, b ≤ w →
      (((Finset.Ioc ⌊x ^ w⌋₊ ⌊Real.exp (L x ^ (-S)) * x ^ w⌋₊).filter
        Nat.Prime).card : ℝ) ≤
        (w⁻¹ + eps) * L x ^ (-S) * x ^ w / L x := by
  obtain ⟨K, hK, hIntervals⟩ :=
    prime_interval_count_le hC (S + 3) 1 (by linarith) (by norm_num)
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hIntervals
  let Cerr : ℝ := K * (Real.exp 1 + 1) * b ^ (-(S + 3))
  let δlim : ℝ := min 1 (eps * b / 4)
  have hCerr : 0 < Cerr := by positivity
  have hδlim : 0 < δlim := by
    apply lt_min one_pos
    positivity
  have hL2 : Tendsto (fun x : ℝ => L x ^ (-2 : ℝ)) atTop (nhds 0) := by
    change Tendsto (fun x : ℝ => Real.log x ^ (-2 : ℝ)) atTop (nhds 0)
    exact (_root_.tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
      Real.tendsto_log_atTop
  have herrorSmall : ∀ᶠ x : ℝ in atTop, Cerr * L x ^ (-2 : ℝ) < eps / 4 :=
    (hL2.const_mul Cerr).eventually
      (Iio_mem_nhds (by simpa using div_pos heps (by norm_num : (0 : ℝ) < 4)))
  have hdeltaZero : Tendsto (fun x : ℝ => L x ^ (-S)) atTop (nhds 0) := by
    change Tendsto (fun x : ℝ => Real.log x ^ (-S)) atTop (nhds 0)
    exact (_root_.tendsto_rpow_neg_atTop hS).comp Real.tendsto_log_atTop
  have hdeltaSmall : ∀ᶠ x : ℝ in atTop, L x ^ (-S) < δlim :=
    hdeltaZero.eventually (Iio_mem_nhds hδlim)
  have hLlarge : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := by
    simpa [Analytic.L] using
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hxLarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hpowerLarge : ∀ᶠ x : ℝ in atTop, max 2 Y₀ ≤ x ^ b := by
    exact (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (max 2 Y₀))
  filter_upwards [herrorSmall, hdeltaSmall, hLlarge, hxLarge, hpowerLarge]
    with x herr hδsmall hL hx hxb
  intro w hbw
  let delta : ℝ := L x ^ (-S)
  let Y : ℝ := x ^ w
  let Z : ℝ := Real.exp delta * Y
  let P : ℝ := delta * Y / L x
  have hLpos : 0 < L x := by linarith
  have hxpos : 0 < x := by linarith
  have hxgt : 1 < x := by linarith
  have hδlim' : delta < δlim := hδsmall
  have hδ1 : delta ≤ 1 := by
    exact (hδlim'.le.trans (min_le_left _ _))
  have hδb : delta ≤ eps * b / 4 := by
    exact hδlim'.le.trans (min_le_right _ _)
  have hδpos : 0 < delta := Real.rpow_pos_of_pos hLpos _
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact Real.rpow_pos_of_pos hxpos _
  have hxbY : x ^ b ≤ Y := by
    dsimp [Y]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hbw
  have hY2 : 2 ≤ Y := (le_trans (le_max_left _ _) hxb).trans hxbY
  have hYY₀ : Y₀ ≤ Y := (le_trans (le_max_right _ _) hxb).trans hxbY
  have hExpLower : 1 ≤ Real.exp delta := by
    have h := Real.add_one_le_exp delta
    linarith
  have hYZ : Y ≤ Z := by
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_right hExpLower hYpos.le]
  have hExpUpper : Real.exp delta ≤ Real.exp 1 := Real.exp_le_exp.mpr hδ1
  have hZupper : Z ≤ Real.exp 1 * Y := by
    dsimp [Z]
    exact mul_le_mul_of_nonneg_right hExpUpper hYpos.le
  have hZpos : 0 < Z := mul_pos (Real.exp_pos _) hYpos
  have hlogYeq : Real.log Y = w * L x := by
    simpa [Y, Analytic.L] using (Real.log_rpow hxpos w)
  have hlogYpos : 0 < Real.log Y := Real.log_pos (by linarith [hY2])
  have hbLpos : 0 < b * L x := mul_pos hb hLpos
  have hbLle : b * L x ≤ Real.log Y := by
    rw [hlogYeq]
    exact mul_le_mul_of_nonneg_right hbw hLpos.le
  have hlogYleZ : Real.log Y ≤ Real.log Z := Real.log_le_log hYpos hYZ
  have hlogZpos : 0 < Real.log Z := hlogYpos.trans_le hlogYleZ
  have hbLleZ : b * L x ≤ Real.log Z := hbLle.trans hlogYleZ
  have hApos : 0 < S + 3 := by linarith
  have hAneg : -(S + 3) ≤ 0 := by linarith
  have hpowY : (Real.log Y) ^ (-(S + 3)) ≤ (b * L x) ^ (-(S + 3)) :=
    Real.rpow_le_rpow_of_nonpos hbLpos hbLle hAneg
  have hpowZ : (Real.log Z) ^ (-(S + 3)) ≤ (b * L x) ^ (-(S + 3)) :=
    Real.rpow_le_rpow_of_nonpos hbLpos hbLleZ hAneg
  have hbaseZ : Z * (Real.log Z) ^ (-(S + 3)) ≤
      Real.exp 1 * Y * (b * L x) ^ (-(S + 3)) := by
    calc
      _ ≤ (Real.exp 1 * Y) * (b * L x) ^ (-(S + 3)) :=
        mul_le_mul hZupper hpowZ (by positivity) (by positivity)
      _ = _ := by ring
  have hbaseY : Y * (Real.log Y) ^ (-(S + 3)) ≤
      Y * (b * L x) ^ (-(S + 3)) :=
    mul_le_mul_of_nonneg_left hpowY hYpos.le
  have herrorRaw : K * Z * (Real.log Z) ^ (-(S + 3)) +
      K * Y * (Real.log Y) ^ (-(S + 3)) ≤
      K * (Real.exp 1 + 1) * Y * (b * L x) ^ (-(S + 3)) := by
    have hZ := mul_le_mul_of_nonneg_left hbaseZ hK.le
    have hY := mul_le_mul_of_nonneg_left hbaseY hK.le
    nlinarith [hZ, hY]
  have herrorBound : K * Z * (Real.log Z) ^ (-(S + 3)) +
      K * Y * (Real.log Y) ^ (-(S + 3)) ≤ Cerr * L x ^ (-2 : ℝ) * P := by
    calc
      _ ≤ K * (Real.exp 1 + 1) * Y * (b * L x) ^ (-(S + 3)) := herrorRaw
      _ = Cerr * L x ^ (-2 : ℝ) * P := by
        rw [rpow_short_interval_error_identity hb hLpos]
        dsimp [Cerr, P, delta]
        ring
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have herrorTarget : K * Z * (Real.log Z) ^ (-(S + 3)) +
      K * Y * (Real.log Y) ^ (-(S + 3)) ≤ eps / 4 * P := by
    calc
      _ ≤ Cerr * L x ^ (-2 : ℝ) * P := herrorBound
      _ ≤ eps / 4 * P := by
        calc
          Cerr * L x ^ (-2 : ℝ) * P = (Cerr * L x ^ (-2 : ℝ)) * P := by ring
          _ ≤ eps / 4 * P := mul_le_mul_of_nonneg_right herr.le hPpos.le
  have hdeltaW : delta ≤ eps * w / 4 := by
    calc
      delta ≤ eps * b / 4 := hδb
      _ ≤ eps * w / 4 := by nlinarith
  have hdeltaSq : delta ^ 2 ≤ eps / 4 * delta * w := by
    calc
      delta ^ 2 = delta * delta := by ring
      _ ≤ (eps * w / 4) * delta := mul_le_mul_of_nonneg_right hdeltaW hδpos.le
      _ = eps / 4 * delta * w := by ring
  have hExtra : delta ^ 2 * Y / (w * L x) ≤ eps / 4 * P := by
    have hwpos : 0 < w := hb.trans_le hbw
    have hδdiv : delta ^ 2 / w ≤ eps / 4 * delta := (div_le_iff₀ hwpos).2 (by nlinarith [hdeltaSq])
    rw [show delta ^ 2 * Y / (w * L x) = (delta ^ 2 / w) * (Y / L x) by
      field_simp [ne_of_gt hwpos, ne_of_gt hLpos]]
    rw [show eps / 4 * P = (eps / 4 * delta) * (Y / L x) by
      dsimp [P]
      field_simp [ne_of_gt hLpos]]
    exact mul_le_mul_of_nonneg_right hδdiv (by positivity)
  have hliCell : (Z - Y) / Real.log Y ≤ P / w + eps / 4 * P := by
    have hwpos : 0 < w := hb.trans_le hbw
    rw [hlogYeq]
    calc
      (Z - Y) / (w * L x) = (Real.exp delta - 1) * Y / (w * L x) := by
        dsimp [Z]
        ring
      _ ≤ (delta + delta ^ 2) * Y / (w * L x) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (exp_delta_le_quadratic hδpos.le hδ1) hYpos.le
      _ = delta * Y / (w * L x) + delta ^ 2 * Y / (w * L x) := by ring
      _ ≤ P / w + eps / 4 * P := by
        rw [show P / w = delta * Y / (w * L x) by
          dsimp [P]
          field_simp [ne_of_gt hwpos, ne_of_gt hLpos]]
        exact add_le_add le_rfl hExtra
  have hcount := hY₀ Y hYY₀ Z hYZ
  have hli := li_interval_upper Y Z hY2 hYZ
  have hfinal : ((w⁻¹ + eps) * P) =
      (w⁻¹ + eps) * L x ^ (-S) * x ^ w / L x := by
    dsimp [P, delta, Y]
    ring
  calc
    (((Finset.Ioc ⌊x ^ w⌋₊ ⌊Real.exp (L x ^ (-S)) * x ^ w⌋₊).filter
        Nat.Prime).card : ℝ) ≤
      li Z - li Y + K * Z * Real.log Z ^ (-(S + 3)) +
        K * Y * Real.log Y ^ (-(S + 3)) := hcount
    _ ≤ P / w + eps / 2 * P := by linarith [hli, herrorTarget]
    _ ≤ (w⁻¹ + eps) * P := by
      have hwpos : 0 < w := hb.trans_le hbw
      have hdiv : P / w = w⁻¹ * P := by field_simp [ne_of_gt hwpos]
      rw [hdiv]
      nlinarith [hPpos]
    _ = (w⁻¹ + eps) * L x ^ (-S) * x ^ w / L x := hfinal

set_option maxHeartbeats 800000 in
theorem roughLogCellLastChoices_count_le (hC : ClassicalInputs)
    {b S eta : ℝ} (hb : 0 < b) (hS : 0 < S) (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, ∀ w : ℝ, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ x ^ b < (p : ℝ)) →
      ∀ k (f : Fin k → PrimeLabel P),
        (roughLogCellLastChoices x S w P f).Nonempty →
        ((roughLogCellLastChoices x S w P f).card : ℝ) ≤
          ((Real.log (x ^ w / (tupleTailProduct f : ℝ)) / L x)⁻¹ + eta) *
            L x ^ (-S) * (x ^ w / (tupleTailProduct f : ℝ)) / L x := by
  obtain hprime := primeShortCellUpper hC (b := b / 2) (S := S) (eps := eta)
    (by linarith) hS heta
  have hLbig : ∀ᶠ x : ℝ in atTop, max 1 (2 / b) ≤ L x := by
    simpa [Analytic.L] using
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2 / b)))
  have hxlarge : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  filter_upwards [hprime, hLbig, hxlarge] with x hprimeX hL hx
  intro w P hP k f hnemp
  let Qn : ℕ := tupleTailProduct f
  let Q : ℝ := Qn
  let Y : ℝ := x ^ w
  let delta : ℝ := L x ^ (-S)
  let lo : ℝ := Y / Q
  let s : ℝ := Real.log lo / L x
  have hx0 : 0 < x := by linarith
  have hLpos : 0 < L x := by
    have := Real.log_pos hx
    simpa [Analytic.L] using this
  have hdeltaPos : 0 < delta := Real.rpow_pos_of_pos hLpos _
  have hdeltaLe : delta ≤ 1 := by
    dsimp [delta]
    have hLone : 1 ≤ L x := (le_max_left 1 (2 / b)).trans hL
    exact Real.rpow_le_one_of_one_le_of_nonpos hLone (by linarith)
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hQnat : 0 < Qn := by
    dsimp [Qn, tupleTailProduct]
    apply Finset.prod_pos
    intro i hi
    exact (hP (f i).val (f i).property).1.pos
  have hQpos : 0 < Q := by dsimp [Q]; exact_mod_cast hQnat
  have hQcast : (Qn : ℝ) = Q := rfl
  have hloPos : 0 < lo := div_pos hYpos hQpos
  obtain ⟨q, hqmem⟩ := hnemp
  have hqparts := Finset.mem_filter.mp hqmem
  have hqGood := hP q.val q.property
  have hqProdNat := hqparts.2
  have hqCell := Finset.mem_Ioc.mp hqProdNat
  have hNatLower : Y < ((q.val * Qn : ℕ) : ℝ) := by
    have hfloorLt : ⌊Y⌋₊ < q.val * Qn := hqCell.1
    have hfloorReal : (⌊Y⌋₊ : ℝ) < ((q.val * Qn : ℕ) : ℝ) := by exact_mod_cast hfloorLt
    have hyfloor : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
    have hnatStep : ⌊Y⌋₊ + 1 ≤ q.val * Qn := by omega
    have hcastStep : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ ((q.val * Qn : ℕ) : ℝ) := by exact_mod_cast hnatStep
    rw [Nat.cast_add, Nat.cast_one] at hcastStep
    linarith
  have hNatUpper : ((q.val * Qn : ℕ) : ℝ) ≤ Real.exp delta * Y := by
    have hfloorLe : q.val * Qn ≤ ⌊Real.exp delta * Y⌋₊ := hqCell.2
    have hcastFloor : ((q.val * Qn : ℕ) : ℝ) ≤ (⌊Real.exp delta * Y⌋₊ : ℝ) := by exact_mod_cast hfloorLe
    exact hcastFloor.trans (Nat.floor_le (by positivity))
  have hbase : x ^ b * Q ≤ Real.exp delta * Y := by
    have hqlo : x ^ b < (q.val : ℝ) := hqGood.2
    have hmul : x ^ b * Q ≤ (q.val : ℝ) * Q :=
      mul_le_mul_of_nonneg_right hqlo.le hQpos.le
    have hcastUpper : (q.val : ℝ) * Q ≤ Real.exp delta * Y := by
      simpa [Q, Qn, Nat.cast_mul] using hNatUpper
    exact hmul.trans hcastUpper
  have hloLower : x ^ b / Real.exp delta ≤ lo := by
    change x ^ b / Real.exp delta ≤ Y / Q
    rw [div_le_div_iff₀ (Real.exp_pos delta) hQpos]
    simpa [mul_comm] using hbase
  have hlogLower : b * L x - delta ≤ Real.log lo := by
    have hLog := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hx0 b) (Real.exp_pos delta)) hloLower
    have hleft : Real.log (x ^ b / Real.exp delta) = b * L x - delta := by
      rw [Real.log_div (Real.rpow_pos_of_pos hx0 b).ne' (Real.exp_pos delta).ne',
        Real.log_rpow hx0 b, Real.log_exp]
      simp [Analytic.L]
    simpa [hleft] using hLog
  have hsLower : b / 2 ≤ s := by
    dsimp [s]
    apply (le_div_iff₀ hLpos).2
    have hbL : 2 ≤ b * L x := by
      have hratio : 2 / b ≤ L x := (le_max_right 1 (2 / b)).trans hL
      have hmul : 2 ≤ L x * b := (div_le_iff₀ hb).1 hratio
      nlinarith
    have hdeltaVs : delta ≤ b * L x / 2 := by nlinarith [hdeltaLe, hbL]
    nlinarith [hlogLower]
  have hpow : x ^ s = lo := by
    have hlogEq : Real.log (x ^ s) = Real.log lo := by
      rw [Real.log_rpow hx0]
      dsimp [s]
      change (Real.log lo / Real.log x) * Real.log x = Real.log lo
      field_simp [ne_of_gt (Real.log_pos hx)]
    apply le_antisymm
    · exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hx0 s) hloPos).1 hlogEq.le
    · exact (Real.log_le_log_iff hloPos (Real.rpow_pos_of_pos hx0 s)).1 hlogEq.symm.le
  have hImage : (roughLogCellLastChoices x S w P f).image Subtype.val ⊆
      ((Finset.Ioc ⌊x ^ s⌋₊ ⌊Real.exp delta * x ^ s⌋₊).filter Nat.Prime) := by
    intro q' hq'
    obtain ⟨q', hqChoice, rfl⟩ := Finset.mem_image.mp hq'
    have hqchoice := Finset.mem_filter.mp hqChoice
    have hqprime := (hP q'.val q'.property).1
    have hqProd := hqchoice.2
    have hqIoc := Finset.mem_Ioc.mp hqProd
    have hYq : Y < ((q'.val * Qn : ℕ) : ℝ) := by
      have hfloorLt : ⌊Y⌋₊ < q'.val * Qn := hqIoc.1
      have hfloorReal : (⌊Y⌋₊ : ℝ) < ((q'.val * Qn : ℕ) : ℝ) := by exact_mod_cast hfloorLt
      have hyfloor : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
      have hnatStep : ⌊Y⌋₊ + 1 ≤ q'.val * Qn := by omega
      have hcastStep : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ ((q'.val * Qn : ℕ) : ℝ) := by exact_mod_cast hnatStep
      rw [Nat.cast_add, Nat.cast_one] at hcastStep
      linarith
    have hZq : ((q'.val * Qn : ℕ) : ℝ) ≤ Real.exp delta * Y := by
      have hfloorLe : q'.val * Qn ≤ ⌊Real.exp delta * Y⌋₊ := hqIoc.2
      have hcastFloor : ((q'.val * Qn : ℕ) : ℝ) ≤ (⌊Real.exp delta * Y⌋₊ : ℝ) := by exact_mod_cast hfloorLe
      exact hcastFloor.trans (Nat.floor_le (by positivity))
    have hYqReal : Y < (q'.val : ℝ) * Q := by
      simpa [Q, Qn, Nat.cast_mul] using hYq
    have hZqReal : (q'.val : ℝ) * Q ≤ Real.exp delta * Y := by
      simpa [Q, Qn, Nat.cast_mul] using hZq
    have hqlo : lo < (q'.val : ℝ) := by
      change Y / Q < (q'.val : ℝ)
      exact (div_lt_iff₀ hQpos).2 (by simpa [mul_comm] using hYqReal)
    have hqhi : (q'.val : ℝ) ≤ Real.exp delta * lo := by
      have hqhi' : (q'.val : ℝ) ≤ (Real.exp delta * Y) / Q :=
        (le_div_iff₀ hQpos).2 hZqReal
      calc
        (q'.val : ℝ) ≤ (Real.exp delta * Y) / Q := hqhi'
        _ = Real.exp delta * lo := by dsimp [lo]; ring
    have hqLoNat : ⌊x ^ s⌋₊ < q'.val := by
      by_contra hnot
      have hqNat : q'.val ≤ ⌊x ^ s⌋₊ := Nat.le_of_not_gt hnot
      have hqReal : (q'.val : ℝ) ≤ (⌊x ^ s⌋₊ : ℝ) := by exact_mod_cast hqNat
      have hxpowNonneg : 0 ≤ x ^ s := (Real.rpow_pos_of_pos hx0 s).le
      have hfloorLe : (⌊x ^ s⌋₊ : ℝ) ≤ x ^ s := Nat.floor_le hxpowNonneg
      rw [hpow] at hfloorLe hqReal
      exact (not_le_of_gt hqlo) (hqReal.trans hfloorLe)
    have hqHiNat : q'.val ≤ ⌊Real.exp delta * x ^ s⌋₊ := by
      apply (Nat.le_floor_iff (by positivity)).2
      have hqhi' : (q'.val : ℝ) ≤ Real.exp delta * x ^ s := by
        calc
          (q'.val : ℝ) ≤ Real.exp delta * lo := hqhi
          _ = Real.exp delta * x ^ s := by rw [← hpow]
      exact hqhi'
    change q'.val ∈
      ((Finset.Ioc ⌊x ^ s⌋₊ ⌊Real.exp delta * x ^ s⌋₊).filter Nat.Prime)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hqLoNat,hqHiNat⟩,hqprime⟩
  have hcardImage : (roughLogCellLastChoices x S w P f).card =
      ((roughLogCellLastChoices x S w P f).image Subtype.val).card :=
    (Finset.card_image_of_injective _ Subtype.val_injective).symm
  have hcell := hprimeX s hsLower
  have hcardle := Finset.card_le_card hImage
  have hcardReal : ((roughLogCellLastChoices x S w P f).card : ℝ) ≤
      ((Finset.Ioc ⌊x ^ s⌋₊ ⌊Real.exp (L x ^ (-S)) * x ^ s⌋₊).filter Nat.Prime).card := by
    exact_mod_cast (hcardImage ▸ hcardle)
  have hcount := hcardReal.trans hcell
  rw [show L x ^ (-S) = delta by rfl, hpow] at hcount
  simpa [lo, s, delta, Y, Q, Qn, tupleTailProduct] using hcount

set_option maxHeartbeats 600000 in
theorem repeatedRoughCellCount_le {X Y Z : ℝ}
    (hX : 2 ≤ X) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    (((Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter
      (fun n => rough X n ∧ ¬ Squarefree n)).card : ℝ) ≤ 2 * Z / X := by
  classical
  let N : ℕ := ⌊X⌋₊ + 1
  let M : ℕ := Nat.sqrt ⌊Z⌋₊
  let D : Finset ℕ := Finset.Icc N M
  let B : Finset ℕ := (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter
    (fun n => rough X n ∧ ¬ Squarefree n)
  let multiples : ℕ → Finset ℕ := fun d =>
    (Finset.Ioc 0 ⌊Z⌋₊).filter (fun n => d ^ 2 ∣ n)
  have hX0 : 0 ≤ X := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hfloorX : 2 ≤ ⌊X⌋₊ := by
    simpa using Nat.floor_mono hX
  have hN2 : 2 ≤ N := by dsimp [N]; omega
  have hcover : B ⊆ D.biUnion multiples := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnI := hn'.1
    have hr := hn'.2.1
    have hnsq := hn'.2.2
    have hnpos : 0 < n := hr.1
    rw [Nat.squarefree_iff_prime_squarefree] at hnsq
    push Not at hnsq
    obtain ⟨p, hp, hpsq⟩ := hnsq
    have hpdvd : p ∣ n := dvd_trans (by simp) hpsq
    have hpX : X < (p : ℝ) := hr.2 p hp hpdvd
    have hpfloor : ⌊X⌋₊ < p := by
      by_contra hnot
      have hple : p ≤ ⌊X⌋₊ := Nat.le_of_not_gt hnot
      have hpcast : (p : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hple
      have hpreal : (p : ℝ) ≤ X := hpcast.trans (Nat.floor_le hX0)
      linarith
    have hpN : N ≤ p := by dsimp [N]; omega
    have hnZ : n ≤ ⌊Z⌋₊ := (Finset.mem_Ioc.mp hnI).2
    have hp2le : p ^ 2 ≤ ⌊Z⌋₊ := by
      have hpn : p * p ≤ n := Nat.le_of_dvd (by omega) hpsq
      exact (by simpa only [pow_two] using hpn.trans hnZ)
    have hpM : p ≤ M := by
      dsimp [M]
      exact (Nat.le_sqrt').2 hp2le
    have hpD : p ∈ D := by
      simp only [D, Finset.mem_Icc]
      exact ⟨hpN, hpM⟩
    have hnMultiples : n ∈ multiples p := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      simp only [Finset.mem_Ioc]
      · exact ⟨by omega,hnZ⟩
      · simpa [pow_two] using hpsq
    exact Finset.mem_biUnion.mpr ⟨p,hpD,hnMultiples⟩
  have hmultCard (d : ℕ) : (multiples d).card = ⌊Z⌋₊ / d ^ 2 := by
    simp only [multiples, Nat.Ioc_filter_dvd_card_eq_div]
  have hcardNat : B.card ≤ ∑ d ∈ D, ⌊Z⌋₊ / d ^ 2 := by
    calc
      B.card ≤ (D.biUnion multiples).card := Finset.card_le_card hcover
      _ ≤ ∑ d ∈ D, (multiples d).card := Finset.card_biUnion_le
      _ = ∑ d ∈ D, ⌊Z⌋₊ / d ^ 2 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hmultCard d
  have hcardReal : (B.card : ℝ) ≤
      ∑ d ∈ D, (((⌊Z⌋₊ / d ^ 2 : ℕ) : ℝ)) := by exact_mod_cast hcardNat
  have hfloorZ : (⌊Z⌋₊ : ℝ) ≤ Z := Nat.floor_le hZ0
  have hsumReal :
      (∑ d ∈ D, (((⌊Z⌋₊ / d ^ 2 : ℕ) : ℝ))) ≤
        Z * ∑ d ∈ D, 1 / (d : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ d ∈ D, Z / (d : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hdpos : 0 < (d : ℝ) := by
          have hdN := (Finset.mem_Icc.mp (by simpa [D] using hd)).1
          exact_mod_cast (Nat.lt_of_lt_of_le (by omega : 0 < N) hdN)
        have hcastdiv0 : ((⌊Z⌋₊ / d ^ 2 : ℕ) : ℝ) ≤
            (⌊Z⌋₊ : ℝ) / ((d ^ 2 : ℕ) : ℝ) :=
          Nat.cast_div_le (m := ⌊Z⌋₊) (n := d ^ 2) (α := ℝ)
        have hcastdiv : ((⌊Z⌋₊ / d ^ 2 : ℕ) : ℝ) ≤
            (⌊Z⌋₊ : ℝ) / (d : ℝ) ^ 2 := by
          have hdcast : ((d ^ 2 : ℕ) : ℝ) = (d : ℝ) ^ 2 := by norm_cast
          rw [hdcast] at hcastdiv0
          exact hcastdiv0
        exact hcastdiv.trans (div_le_div_of_nonneg_right hfloorZ (by positivity))
      _ = Z * ∑ d ∈ D, 1 / (d : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
  have htail := reciprocal_square_tail_finset N M hN2
  have hNminus : (N : ℝ) - 1 = (⌊X⌋₊ : ℝ) := by
    dsimp [N]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have htail' : ∑ d ∈ D, 1 / (d : ℝ) ^ 2 ≤ 1 / (⌊X⌋₊ : ℝ) := by
    simpa [D, hNminus] using htail
  have hcountFloor : (B.card : ℝ) ≤ Z / (⌊X⌋₊ : ℝ) := by
    calc
      (B.card : ℝ) ≤ ∑ d ∈ D, (((⌊Z⌋₊ / d ^ 2 : ℕ) : ℝ)) := hcardReal
      _ ≤ Z * ∑ d ∈ D, 1 / (d : ℝ) ^ 2 := hsumReal
      _ ≤ Z * (1 / (⌊X⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left htail' hZ0
      _ = Z / (⌊X⌋₊ : ℝ) := by ring
  have hfloorLower : X / 2 ≤ (⌊X⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one X
    nlinarith
  have hfloorPos : 0 < (⌊X⌋₊ : ℝ) := by positivity
  have hInv : ((⌊X⌋₊ : ℝ))⁻¹ ≤ (X / 2)⁻¹ :=
    inv_anti₀ (by positivity) hfloorLower
  have hfinal : Z / (⌊X⌋₊ : ℝ) ≤ 2 * Z / X := by
    calc
      Z / (⌊X⌋₊ : ℝ) = Z * (⌊X⌋₊ : ℝ)⁻¹ := by ring
      _ ≤ Z * (X / 2)⁻¹ := mul_le_mul_of_nonneg_left hInv hZ0
      _ = 2 * Z / X := by field_simp [ne_of_gt (by linarith : 0 < X)]
  have hcardB : B = (Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊).filter
      (fun n => rough X n ∧ ¬ Squarefree n) := rfl
  simpa [B, hcardB] using hcountFloor.trans hfinal

set_option maxHeartbeats 600000 in
theorem repeatedRoughCellErrorSmall {b S eps : ℝ}
    (hb : 0 < b) (hS : 0 < S) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ gamma w : ℝ, b ≤ gamma →
      2 * Real.exp (L x ^ (-S)) * x ^ w / x ^ gamma ≤
        eps / 2 * (L x ^ (-S) * x ^ w / L x) := by
  have hdecay : Tendsto (fun x : ℝ => L x ^ (S + 1) / x ^ b) atTop (nhds 0) := by
    have hbase := _root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (S + 1) b (by linarith)
    have hcomp := hbase.comp Real.tendsto_log_atTop
    have heq : (fun x : ℝ => L x ^ (S + 1) / x ^ b) =ᶠ[atTop]
        (fun x : ℝ => L x ^ (S + 1) * Real.exp (-b * L x)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hxpos : 0 < x := by linarith
      rw [Real.rpow_def_of_pos hxpos b]
      simp [Analytic.L, Real.exp_neg, div_eq_mul_inv, mul_comm]
    exact hcomp.congr' heq.symm
  have hRsmall : ∀ᶠ x : ℝ in atTop, 4 * Real.exp 1 * (L x ^ (S + 1) / x ^ b) < eps := by
    have h := (hdecay.const_mul (4 * Real.exp 1)).eventually
      (Iio_mem_nhds (by simpa using heps))
    simpa [mul_comm] using h
  have hdeltaSmall : ∀ᶠ x : ℝ in atTop, L x ^ (-S) < 1 := by
    have h := (_root_.tendsto_rpow_neg_atTop hS).comp Real.tendsto_log_atTop
    change ∀ᶠ x : ℝ in atTop, Real.log x ^ (-S) < 1
    exact h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hLlarge : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := by
    simpa [Analytic.L] using
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hxlarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  filter_upwards [hRsmall, hdeltaSmall, hLlarge, hxlarge]
    with x hR hdelta hL hx
  intro gamma w hbg
  let delta : ℝ := L x ^ (-S)
  let Y : ℝ := x ^ w
  let X : ℝ := x ^ gamma
  let P : ℝ := delta * Y / L x
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := by linarith
  have hδpos : 0 < delta := Real.rpow_pos_of_pos hLpos _
  have hδ1 : delta ≤ 1 := hdelta.le
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hxpos _
  have hXpos : 0 < X := Real.rpow_pos_of_pos hxpos _
  have hxbX : x ^ b ≤ X :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hbg
  have hXpos' : 0 < x ^ b := Real.rpow_pos_of_pos hxpos _
  have hExp : Real.exp delta ≤ Real.exp 1 := Real.exp_le_exp.mpr hδ1
  have hcompare : 2 * Real.exp delta * Y / X ≤ 2 * Real.exp 1 * Y / (x ^ b) := by
    have hInv : X⁻¹ ≤ (x ^ b)⁻¹ := inv_anti₀ hXpos' hxbX
    have hExp2 : 2 * Real.exp delta ≤ 2 * Real.exp 1 :=
      mul_le_mul_of_nonneg_left hExp (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * Real.exp delta * Y / X = (2 * Real.exp delta * Y) * X⁻¹ := by ring
      _ ≤ (2 * Real.exp 1 * Y) * X⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hExp2 hYpos.le) (inv_nonneg.mpr hXpos.le)
      _ ≤ (2 * Real.exp 1 * Y) * (x ^ b)⁻¹ :=
        mul_le_mul_of_nonneg_left hInv (by positivity)
      _ = 2 * Real.exp 1 * Y / (x ^ b) := by ring
  have hpowId : L x ^ (S + 1) * L x ^ (-S) / L x = 1 := by
    rw [Real.rpow_add hLpos, Real.rpow_neg hLpos.le S, Real.rpow_one]
    field_simp [ne_of_gt hLpos]
  have hscaleEq : 2 * Real.exp 1 * Y / (x ^ b) =
      (4 * Real.exp 1 * (L x ^ (S + 1) / x ^ b)) * (P / 2) := by
    dsimp [P, delta]
    calc
      2 * Real.exp 1 * Y / (x ^ b) =
          (2 * Real.exp 1 * Y / (x ^ b)) *
            (L x ^ (S + 1) * L x ^ (-S) / L x) := by rw [hpowId, mul_one]
      _ = (4 * Real.exp 1 * (L x ^ (S + 1) / x ^ b)) *
          ((L x ^ (-S) * Y / L x) / 2) := by ring
      _ = _ := by ring
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hsmall : 2 * Real.exp 1 * Y / (x ^ b) ≤ eps / 2 * P := by
    calc
      _ = (4 * Real.exp 1 * (L x ^ (S + 1) / x ^ b)) * (P / 2) := hscaleEq
      _ ≤ eps * (P / 2) := by
        exact mul_le_mul_of_nonneg_right hR.le (by positivity)
      _ = eps / 2 * P := by ring
  exact hcompare.trans hsmall

set_option maxHeartbeats 600000 in
theorem roughFactorLengthBound {b wMax gap S : ℝ}
    (hb : 0 < b) (hwMax : 0 < wMax) (hgap : 0 < gap) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ gamma w : ℝ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax →
      ∀ n : ℕ, n ∈ roughLogCell x S w → rough (x ^ gamma) n →
        n.primeFactors.card ≤ ⌊wMax / b⌋₊ := by
  let K : ℕ := ⌊wMax / b⌋₊
  let margin : ℝ := b * ((K : ℝ) + 1) - wMax
  have hfloor : wMax / b < (K : ℝ) + 1 := by
    dsimp [K]
    exact Nat.lt_floor_add_one (wMax / b)
  have hmargin : 0 < margin := by
    dsimp [margin]
    have hm := mul_lt_mul_of_pos_left hfloor hb
    have hcancel : b * (wMax / b) = wMax := by field_simp [ne_of_gt hb]
    rw [hcancel] at hm
    linarith
  have hLlarge : ∀ᶠ x : ℝ in atTop, max 1 (2 / margin) ≤ L x := by
    simpa [Analytic.L] using
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2 / margin)))
  have hxlarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  filter_upwards [hLlarge, hxlarge] with x hL hx
  intro gamma w hbg hgw hww n hnCell hnRough
  have hxpos : 0 < x := by linarith
  have hxgt : 1 < x := by linarith
  have hLpos : 0 < L x := by
    have h := Real.log_pos hxgt
    simpa [Analytic.L] using h
  have hLone : 1 ≤ L x := (le_max_left 1 (2 / margin)).trans hL
  have hLmargin : 2 ≤ margin * L x := by
    have hratio : 2 / margin ≤ L x := (le_max_right 1 (2 / margin)).trans hL
    simpa [mul_comm] using (div_le_iff₀ hmargin).1 hratio
  have hgammaPos : 0 < gamma := lt_of_lt_of_le hb hbg
  have hwPos : 0 < w := by linarith
  have hdeltaPos : 0 < L x ^ (-S) := Real.rpow_pos_of_pos hLpos _
  have hdeltaLe : L x ^ (-S) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hLone (by linarith)
  let Y : ℝ := x ^ w
  let Z : ℝ := Real.exp (L x ^ (-S)) * Y
  have hYgt : 1 < Y := by
    dsimp [Y]
    exact Real.one_lt_rpow hxgt hwPos
  have hnLarge : 1 < n := by
    have hnIoc := Finset.mem_Ioc.mp hnCell
    have hfloorYpos : 0 < ⌊Y⌋₊ := Nat.floor_pos.mpr hYgt.le
    have hfloorYone : 1 ≤ ⌊Y⌋₊ := Nat.succ_le_of_lt hfloorYpos
    exact lt_of_le_of_lt hfloorYone hnIoc.1
  have hnpos : n ≠ 0 := by omega
  have hFactorsNonempty : n.primeFactors.Nonempty :=
    (Nat.nonempty_primeFactors).2 hnLarge
  have hfactorLower (p : ℕ) (hp : p ∈ n.primeFactors) :
      x ^ b < (p : ℝ) := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdiv := Nat.dvd_of_mem_primeFactors hp
    have hroughP := hnRough.2 p hprime hdiv
    have hxb : x ^ b ≤ x ^ gamma :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) hbg
    exact hxb.trans_lt hroughP
  have hprodStrict : (x ^ b) ^ n.primeFactors.card < (n : ℝ) := by
    have h := Finset.prod_lt_prod_of_nonempty₀
      (fun _ _ => Real.rpow_pos_of_pos hxpos b)
      (fun p hp => hfactorLower p hp) hFactorsNonempty
    have hconst : ∏ p ∈ n.primeFactors, x ^ b = (x ^ b) ^ n.primeFactors.card := by
      simp
    have hradNat : ∏ p ∈ n.primeFactors, p ≤ n :=
      Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    have hradReal : ∏ p ∈ n.primeFactors, (p : ℝ) ≤ (n : ℝ) := by
      calc
        _ = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by simp
        _ ≤ n := by exact_mod_cast hradNat
    rw [hconst] at h
    exact h.trans_le hradReal
  by_contra hnot
  have hk : K + 1 ≤ n.primeFactors.card := by
    dsimp [K]
    omega
  have hxbase : 1 < x ^ b := Real.one_lt_rpow hxgt hb
  have hpowMono : (x ^ b) ^ (K + 1) ≤ (x ^ b) ^ n.primeFactors.card :=
    pow_le_pow_right₀ hxbase.le hk
  have hlow : (x ^ b) ^ (K + 1) < (n : ℝ) := hpowMono.trans_lt hprodStrict
  have hnCellIoc := Finset.mem_Ioc.mp hnCell
  have hnUpperNat : n ≤ ⌊Z⌋₊ := hnCellIoc.2
  have hnUpperFloor : (n : ℝ) ≤ (⌊Z⌋₊ : ℝ) := by exact_mod_cast hnUpperNat
  have hnUpper : (n : ℝ) ≤ Z := hnUpperFloor.trans (Nat.floor_le (by positivity))
  have hlogLower : ((K + 1 : ℕ) : ℝ) * b * L x < Real.log n := by
    have h := Real.log_lt_log
      (pow_pos (Real.rpow_pos_of_pos hxpos b) (K + 1)) hlow
    rw [Real.log_pow, Real.log_rpow hxpos] at h
    simpa [Analytic.L, mul_assoc] using h
  have hZpos : 0 < Z := by positivity
  have hlogUpper : Real.log n ≤ Real.log Z := Real.log_le_log (by positivity) hnUpper
  have hlogZ : Real.log Z = L x ^ (-S) + w * L x := by
    dsimp [Z, Y]
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hxpos w).ne',
      Real.log_exp, Real.log_rpow hxpos]
    simp [Analytic.L]
  have hlogContr : ((K + 1 : ℕ) : ℝ) * b * L x < L x ^ (-S) + w * L x := by
    calc
      ((K + 1 : ℕ) : ℝ) * b * L x < Real.log n := hlogLower
      _ ≤ Real.log Z := hlogUpper
      _ = L x ^ (-S) + w * L x := hlogZ
  have hmarginL : margin * L x < L x ^ (-S) := by
    have hcoeff : ((K + 1 : ℕ) : ℝ) * b - w = margin + (wMax - w) := by
      dsimp [margin]
      push_cast
      ring
    have hcoeffL : (((K + 1 : ℕ) : ℝ) * b - w) * L x < L x ^ (-S) := by
      nlinarith [hlogContr]
    have hmarginLe : margin * L x ≤
        (((K + 1 : ℕ) : ℝ) * b - w) * L x := by
      rw [hcoeff]
      have hwle : 0 ≤ wMax - w := by linarith
      nlinarith [mul_nonneg hwle hLpos.le]
    exact lt_of_le_of_lt hmarginLe hcoeffL
  linarith [hmarginL,hLmargin,hdeltaLe]

theorem roughCell_card_partition (x S gamma w : ℝ) :
    (((roughLogCell x S w).filter (rough (x ^ gamma))).card : ℝ) ≤
      (((roughLogCell x S w).filter Nat.Prime).card : ℝ) +
      (((roughLogCell x S w).filter
        (fun n => rough (x ^ gamma) n ∧ ¬ Squarefree n)).card : ℝ) +
      ((squarefreeRoughCell x S gamma w).card : ℝ) := by
  classical
  let I := roughLogCell x S w
  let R := I.filter (rough (x ^ gamma))
  let P := I.filter Nat.Prime
  let N := I.filter (fun n => rough (x ^ gamma) n ∧ ¬ Squarefree n)
  let C := squarefreeRoughCell x S gamma w
  have hsubset : R ⊆ (P ∪ N) ∪ C := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hcell := hn'.1
    have hr := hn'.2
    by_cases hp : n.Prime
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      change n ∈ I.filter Nat.Prime
      exact Finset.mem_filter.mpr ⟨hcell,hp⟩
    · by_cases hs : Squarefree n
      · apply Finset.mem_union.mpr
        right
        simp [C, squarefreeRoughCell, I, hcell, hr, hs, hp]
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        change n ∈ I.filter (fun n => rough (x ^ gamma) n ∧ ¬ Squarefree n)
        exact Finset.mem_filter.mpr ⟨hcell,⟨hr,hs⟩⟩
  have hcardNat : R.card ≤ P.card + N.card + C.card := by
    calc
      R.card ≤ ((P ∪ N) ∪ C).card := Finset.card_le_card hsubset
      _ ≤ (P ∪ N).card + C.card := Finset.card_union_le _ _
      _ ≤ P.card + N.card + C.card := by
        have h := Finset.card_union_le P N
        omega
  exact_mod_cast hcardNat

/-- The single remaining step: finite-grid convergence for squarefree prime lists. -/
theorem squarefreeRoughCell_gridUpper (hC : ClassicalInputs)
    (b wMax gap S : ℝ) (hb : 0 < b) (hwMax : 0 < wMax)
    (hgap : 0 < gap) (hS : 0 < S) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ gamma w : ℝ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax →
      ((squarefreeRoughCell x S gamma w).card : ℝ) ≤
        (roughDensity gamma w - w⁻¹ + eps) * L x ^ (-S) * x ^ w / L x := by
  classical
  obtain ⟨eta, heta, hGrid⟩ := tailPrimeGridSimplexUpper hC b wMax gap S
    hb hwMax hgap hS (eps := eps / 2) (by positivity)
  have hFactorLen := roughFactorLengthBound hb hwMax hgap hS
  have hLast := roughLogCellLastChoices_count_le hC hb hS heta
  have hxLarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  filter_upwards [hGrid, hFactorLen, hLast, hxLarge] with x hGridX hFactorX hLastX hx
  intro gamma w hbg hgw hww
  have hxpos : 0 < x := by linarith
  have hxgt : 1 < x := by linarith
  have hgammaPos : 0 < gamma := lt_of_lt_of_le hb hbg
  have hwPos : 0 < w := by linarith
  let Y : ℝ := x ^ w
  let delta : ℝ := L x ^ (-S)
  let upper : ℝ := Real.exp delta * x ^ wMax
  let I : Finset ℕ := roughLogCell x S w
  let C : Finset ℕ := squarefreeRoughCell x S gamma w
  let K : ℕ := ⌊wMax / b⌋₊
  let P : Finset ℕ :=
    (Finset.Icc 1 ⌊upper⌋₊).filter fun p => p.Prime ∧ x ^ gamma < (p : ℝ)
  let scale : ℝ := L x ^ (-S) * x ^ w / L x
  have hLpos : 0 < L x := by
    have h := Real.log_pos hxgt
    simpa [Analytic.L] using h
  have hdeltaPos : 0 < delta := Real.rpow_pos_of_pos hLpos _
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hxpos _
  have hYgt : 1 < Y := Real.one_lt_rpow hxgt hwPos
  have hPgood : ∀ p ∈ P, p.Prime ∧ x ^ gamma < (p : ℝ) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hPrough : ∀ p ∈ P, p.Prime ∧ x ^ b < (p : ℝ) := by
    intro p hp
    have h := hPgood p hp
    have hxb : x ^ b ≤ x ^ gamma :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hbg
    exact ⟨h.1, hxb.trans_lt h.2⟩
  have hZmono : Real.exp delta * x ^ w ≤ upper := by
    dsimp [upper]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hww) (Real.exp_nonneg _)
  have hFactors : ∀ n, n ∈ C → n.primeFactors ⊆ P := by
    intro n hn p hp
    have hnC := Finset.mem_filter.mp hn
    have hrough := hnC.2.1
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := Nat.dvd_of_mem_primeFactors hp
    have hpCut := hrough.2 p hpPrime hpDvd
    have hpLe : p ≤ n := Nat.le_of_mem_primeFactors hp
    have hnIoc := Finset.mem_Ioc.mp hnC.1
    have hnUpper : n ≤ ⌊Real.exp delta * x ^ w⌋₊ := by
      simpa [I, roughLogCell] using hnIoc.2
    have hpUpper : p ≤ ⌊upper⌋₊ :=
      hpLe.trans (hnUpper.trans (Nat.floor_mono hZmono))
    have hpge1 : 1 ≤ p := le_trans (by norm_num : 1 ≤ 2) hpPrime.two_le
    have hpMember : p ∈ Finset.Icc 1 ⌊upper⌋₊ :=
      Finset.mem_Icc.mpr ⟨hpge1, hpUpper⟩
    exact Finset.mem_filter.mpr ⟨hpMember, ⟨hpPrime, hpCut⟩⟩
  have hLenUpper : ∀ n, n ∈ C → n.primeFactors.card ≤ K := by
    intro n hn
    have hnC := Finset.mem_filter.mp hn
    exact hFactorX gamma w hbg hgw hww n hnC.1 hnC.2.1
  have hLenLower : ∀ n, n ∈ C → 2 ≤ n.primeFactors.card := by
    intro n hn
    have hnC := Finset.mem_filter.mp hn
    have hrough := hnC.2.1
    have hsq := hnC.2.2.1
    have hnnotprime := hnC.2.2.2
    have hnIoc := Finset.mem_Ioc.mp hnC.1
    have hfloorYpos : 0 < ⌊Y⌋₊ := Nat.floor_pos.mpr hYgt.le
    have hfloorYone : 1 ≤ ⌊Y⌋₊ := Nat.succ_le_of_lt hfloorYpos
    have hnLarge : 1 < n := lt_of_le_of_lt hfloorYone hnIoc.1
    have hnonempty : n.primeFactors.Nonempty := (Nat.nonempty_primeFactors).2 hnLarge
    have hcardpos : 0 < n.primeFactors.card := Finset.card_pos.mpr hnonempty
    by_contra hlt
    have hcardle : n.primeFactors.card ≤ 1 := by omega
    have hcardone : n.primeFactors.card = 1 := by omega
    have hprimePow : IsPrimePow n :=
      (isPrimePow_iff_card_primeFactors_eq_one).2 hcardone
    have hprime : Nat.Prime n :=
      (Nat.squarefree_and_prime_pow_iff_prime).mp ⟨hsq, hprimePow⟩
    exact hnnotprime hprime
  have hSqTuple := squarefreeRoughCell_tuple_count_bound x S gamma w P K
    hFactors hLenLower hLenUpper
  have hLastCount (l : ℕ) (hl : l ∈ Finset.Icc 2 K) :
      (primeTupleCellFinset I P l).card / (l.factorial : ℝ) ≤
        scale * tailPrimeGridTerm x S w eta P l / (l.factorial : ℝ) := by
    have hTail := primeTupleCell_card_le_tail_sum I P (l - 1)
    have hl2 : 2 ≤ l := (Finset.mem_Icc.mp hl).1
    have hlAdd : (l - 1) + 1 = l := by omega
    have hTailCard : (primeTupleCellFinset I P l).card ≤
        ∑ f : Fin (l - 1) → PrimeLabel P, (roughLogCellLastChoices x S w P f).card := by
      rw [hlAdd] at hTail
      simpa [I, roughLogCellLastChoices] using hTail
    have hTailReal : ((primeTupleCellFinset I P l).card : ℝ) ≤
        ∑ f : Fin (l - 1) → PrimeLabel P,
          ((roughLogCellLastChoices x S w P f).card : ℝ) := by exact_mod_cast hTailCard
    have hSumChoices :
        (∑ f : Fin (l - 1) → PrimeLabel P,
          ((roughLogCellLastChoices x S w P f).card : ℝ)) ≤
          scale * tailPrimeGridTerm x S w eta P l := by
      unfold tailPrimeGridTerm
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro f hf
      by_cases hne : (roughLogCellLastChoices x S w P f).Nonempty
      · have hchoices := hLastX w P hPrough (l - 1) f hne
        have hQnat : 0 < tupleTailProduct f := by
          unfold tupleTailProduct
          apply Finset.prod_pos
          intro i hi
          exact (hPrough (f i).val (f i).property).1.pos
        have hQpos : 0 < (tupleTailProduct f : ℝ) := by exact_mod_cast hQnat
        have hscale :
            ((Real.log (x ^ w / (tupleTailProduct f : ℝ)) / L x)⁻¹ + eta) *
                L x ^ (-S) * (x ^ w / (tupleTailProduct f : ℝ)) / L x =
              scale * (((Real.log (x ^ w / (tupleTailProduct f : ℝ)) / L x)⁻¹ + eta) /
                (tupleTailProduct f : ℝ)) := by
          dsimp [scale]
          field_simp [ne_of_gt hLpos, ne_of_gt hQpos]
          
        simpa [hne, scale] using hchoices.trans_eq hscale
      · have hnil : roughLogCellLastChoices x S w P f = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hne, hnil]
    have hfactorpos : 0 < (l.factorial : ℝ) := by positivity
    have hdiv := div_le_div_of_nonneg_right (hTailReal.trans hSumChoices)
      (by positivity : 0 ≤ (l.factorial : ℝ))
    simpa [div_eq_mul_inv, mul_assoc] using hdiv
  have hSqMass : (C.card : ℝ) ≤ scale * tailPrimeGridMass x S w eta P K := by
    calc
      (C.card : ℝ) ≤
          ∑ l ∈ Finset.Icc 2 K,
            (primeTupleCellFinset I P l).card / (l.factorial : ℝ) := hSqTuple
      _ ≤ ∑ l ∈ Finset.Icc 2 K,
            scale * tailPrimeGridTerm x S w eta P l / (l.factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro l hl
        exact hLastCount l hl
      _ = scale * tailPrimeGridMass x S w eta P K := by
        rw [tailPrimeGridMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
  have hratio1 : w / gamma ≤ wMax / gamma :=
    div_le_div_of_nonneg_right hww (by positivity)
  have hInv : gamma⁻¹ ≤ b⁻¹ := inv_anti₀ hb hbg
  have hratio2 : wMax / gamma ≤ wMax / b := by
    calc
      wMax / gamma = wMax * gamma⁻¹ := by ring
      _ ≤ wMax * b⁻¹ := mul_le_mul_of_nonneg_left hInv hwMax.le
      _ = wMax / b := by ring
  have hKfloor : ⌊w / gamma⌋₊ ≤ K := by
    dsimp [K]
    exact Nat.floor_mono (hratio1.trans hratio2)
  have hDensityEq := roughDensity_eq_inv_add_cutoff hgammaPos hKfloor
  have hDensitySum :
      (∑ l ∈ Finset.Icc 2 K, densityTerm gamma w l / (l.factorial : ℝ)) =
        roughDensity gamma w - w⁻¹ := by linarith
  have hGridMass := hGridX gamma w hbg hgw hww P hPgood
  have hcoeff :
      (∑ l ∈ Finset.Icc 2 K, densityTerm gamma w l / (l.factorial : ℝ)) + eps / 2 ≤
        roughDensity gamma w - w⁻¹ + eps := by rw [hDensitySum]; linarith
  calc
    (C.card : ℝ) ≤ scale * tailPrimeGridMass x S w eta P K := hSqMass
    _ ≤ scale * ((∑ l ∈ Finset.Icc 2 K,
          densityTerm gamma w l / (l.factorial : ℝ)) + eps / 2) :=
        mul_le_mul_of_nonneg_left hGridMass (by positivity)
    _ ≤ scale * (roughDensity gamma w - w⁻¹ + eps) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = (roughDensity gamma w - w⁻¹ + eps) * L x ^ (-S) * x ^ w / L x := by
        dsimp [scale, C]
        ring

theorem roughCellDensityTask_proof : RoughCellDensityTask := by
  intro hC b wMax gap S hb hwMax hgap hS eps heps
  have hthird : 0 < eps / 3 := by positivity
  have htwothirds : 0 < 2 * eps / 3 := by positivity
  obtain hprime := primeShortCellUpper hC (b := b) (S := S) (eps := eps / 3) hb hS hthird
  obtain hrepeat := repeatedRoughCellErrorSmall (b := b) (S := S) (eps := 2 * eps / 3) hb hS htwothirds
  obtain hgrid := squarefreeRoughCell_gridUpper hC b wMax gap S hb hwMax hgap hS hthird
  have hxb : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ b :=
    tendsto_rpow_atTop hb |>.eventually (eventually_ge_atTop 2)
  have hx : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  filter_upwards [hprime, hrepeat, hgrid, hxb, hx] with x hp hr hg hxb hx
  intro gamma w hbg hgw hww
  have hxpos : 0 < x := by linarith
  have hxgt : 1 < x := by linarith
  have hgamma : 0 < gamma := lt_of_lt_of_le hb hbg
  have hwpos : 0 < w := by linarith
  let Y : ℝ := x ^ w
  let delta : ℝ := L x ^ (-S)
  let Z : ℝ := Real.exp delta * Y
  let X : ℝ := x ^ gamma
  let P : ℝ := delta * Y / L x
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hxpos _
  have hYone : 1 ≤ Y := (Real.one_lt_rpow hxgt hwpos).le
  have hLpos : 0 < L x := by
    have h := Real.log_pos hxgt
    simpa [Analytic.L] using h
  have hdeltaPos : 0 < delta := Real.rpow_pos_of_pos hLpos _
  have hExpGe : 1 ≤ Real.exp delta := by linarith [Real.add_one_le_exp delta]
  have hYZ : Y ≤ Z := by
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_right hExpGe hYpos.le]
  have hX2 : 2 ≤ X := by
    have hmono : x ^ b ≤ x ^ gamma :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hbg
    exact hxb.trans hmono
  have hPpos : 0 < P := by dsimp [P, delta]; positivity
  have hPrime : (((roughLogCell x S w).filter Nat.Prime).card : ℝ) ≤
      (w⁻¹ + eps / 3) * P := by
    have h := hp w (by linarith [hbg, hgw])
    calc
      (((roughLogCell x S w).filter Nat.Prime).card : ℝ) ≤
          (w⁻¹ + eps / 3) * L x ^ (-S) * x ^ w / L x := by
        simpa [roughLogCell] using h
      _ = (w⁻¹ + eps / 3) * P := by dsimp [P, delta, Y]; ring
  have hRepeat : (((roughLogCell x S w).filter
      (fun n => rough (x ^ gamma) n ∧ ¬ Squarefree n)).card : ℝ) ≤
        eps / 3 * P := by
    have hcount := repeatedRoughCellCount_le hX2 hYone hYZ
    have hsmall := hr gamma w hbg
    have hsmall' : 2 * Z / X ≤ (2 * eps / 3 / 2) * P := by
      calc
        2 * Z / X = 2 * Real.exp delta * x ^ w / x ^ gamma := by dsimp [Z, Y, X]; ring
        _ ≤ (2 * eps / 3 / 2) * P := by simpa [P, delta, Y] using hsmall
    have h := hcount.trans hsmall'
    have hcoeff : 2 * eps / 3 / 2 = eps / 3 := by ring
    rw [hcoeff] at h
    simpa [roughLogCell] using h
  have hSquarefree : ((squarefreeRoughCell x S gamma w).card : ℝ) ≤
      (roughDensity gamma w - w⁻¹ + eps / 3) * P := by
    have h := hg gamma w hbg hgw hww
    calc
      _ ≤ (roughDensity gamma w - w⁻¹ + eps / 3) * L x ^ (-S) * x ^ w / L x := h
      _ = (roughDensity gamma w - w⁻¹ + eps / 3) * P := by dsimp [P, delta, Y]; ring
  have hPartition := roughCell_card_partition x S gamma w
  have hsum := hPartition.trans (add_le_add (add_le_add hPrime hRepeat) hSquarefree)
  have hresult :
      (w⁻¹ + eps / 3) * P + eps / 3 * P +
        (roughDensity gamma w - w⁻¹ + eps / 3) * P =
          (roughDensity gamma w + eps) * P := by ring
  have hfinal :
      (((roughLogCell x S w).filter (rough (x ^ gamma))).card : ℝ) ≤
        (roughDensity gamma w + eps) * P := by
    rw [hresult] at hsum
    exact hsum
  calc
    (((roughLogCell x S w).filter (rough (x ^ gamma))).card : ℝ) ≤
        (roughDensity gamma w + eps) * P := hfinal
    _ = (roughDensity gamma w + eps) * L x ^ (-S) * x ^ w / L x := by
      dsimp [P, delta, Y]
      ring

/-- The snapshot cell estimate has exactly the fixed task type. -/
example : P8Core.RoughCellDensityTask = RoughCellDensityTask := rfl

end Erdos821.P8Grid

namespace Erdos821.P8Core

/-- The delivered short-cell estimate has exactly the fixed task type. -/
theorem roughCellDensityTask_proof : RoughCellDensityTask :=
  P8Grid.roughCellDensityTask_proof

end Erdos821.P8Core
