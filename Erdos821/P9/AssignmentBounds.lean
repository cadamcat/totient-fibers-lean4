import Erdos821.P9.Assignment
import Erdos821.P9.PairEulerProduct

open scoped BigOperators
open Filter

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every slot value stays below the upper endpoint of its band, including the rough slot. -/
theorem slotValue_le_bandUpper (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (jstar : ℕ) (s : C.bands.Slot x)
    (v : C.bands.SlotValue x jstar s) :
    (v.val : ℝ) ≤ Real.exp (C.bands.c₂ * C.bands.scale x s.1.val) := by
  let lo := Real.exp (C.bands.c₁ * C.bands.scale x s.1.val)
  let hi := Real.exp (C.bands.c₂ * C.bands.scale x s.1.val)
  have hinterval : v.val ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := by
    by_cases hs : s.1.val = jstar ∧ s.2.val = 0
    · have hv : v.val ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (Erdos821.Blueprint.Analytic.rough (Erdos821.Blueprint.Analytic.W x)) := by
        simpa [lo, hi, Erdos821.Blueprint.BandData.slotValues, hs] using v.property
      exact (Finset.mem_filter.mp hv).1
    · have hv : v.val ∈ C.bands.band x s.1.val := by
        simpa [lo, hi, Erdos821.Blueprint.BandData.slotValues, hs] using v.property
      exact (Finset.mem_filter.mp hv).1
  have hnat : v.val ≤ ⌊hi⌋₊ := (Finset.mem_Icc.mp hinterval).2
  have hcast : (v.val : ℝ) ≤ (⌊hi⌋₊ : ℝ) := by exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le (Real.exp_nonneg _))


lemma one_sub_product_le_sum {s : Finset ℕ} (f : ℕ → ℝ)
    (hf0 : ∀ p ∈ s, 0 ≤ f p) (hf1 : ∀ p ∈ s, f p ≤ 1) :
    1 - ∏ p ∈ s, (1 - f p) ≤ ∑ p ∈ s, f p := by
  classical
  revert hf0 hf1
  induction s using Finset.induction_on with
  | empty => intro; simp
  | @insert p s hp ih =>
      intro hf0 hf1
      have hf0s : ∀ q ∈ s, 0 ≤ f q := by
        intro q hq
        exact hf0 q (Finset.mem_insert_of_mem hq)
      have hf1s : ∀ q ∈ s, f q ≤ 1 := by
        intro q hq
        exact hf1 q (Finset.mem_insert_of_mem hq)
      have hprod0 : 0 ≤ ∏ q ∈ s, (1 - f q) :=
        Finset.prod_nonneg (by intro q hq; linarith [hf1s q hq])
      have hprod1 : ∏ q ∈ s, (1 - f q) ≤ 1 :=
        Finset.prod_le_one₀
          (by intro q hq; linarith [hf1s q hq])
          (by intro q hq; linarith [hf0s q hq])
      have hrem : 0 ≤ 1 - ∏ q ∈ s, (1 - f q) := sub_nonneg.mpr hprod1
      have hmul : (1 - f p) * (1 - ∏ q ∈ s, (1 - f q)) ≤
          1 - ∏ q ∈ s, (1 - f q) := by
        calc
          (1 - f p) * (1 - ∏ q ∈ s, (1 - f q)) ≤
              1 * (1 - ∏ q ∈ s, (1 - f q)) :=
            mul_le_mul_of_nonneg_right
              (by linarith [hf0 p (Finset.mem_insert_self p s)]) hrem
          _ = 1 - ∏ q ∈ s, (1 - f q) := by ring
      simp only [Finset.prod_insert hp, Finset.sum_insert hp]
      have halg : 1 - ((1 - f p) * ∏ q ∈ s, (1 - f q)) =
          f p + (1 - f p) * (1 - ∏ q ∈ s, (1 - f q)) := by ring
      rw [halg]
      simpa [add_comm] using add_le_add_left (hmul.trans (ih hf0s hf1s)) (f p)


abbrev MicroIndexType (C : Erdos821.Blueprint.CandidateData) (x : ℝ) :=
  {j : ℕ // j ∈ Finset.Ico C.micro (C.bands.last x + 1)}

noncomputable def microSlotIndexEquiv (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) : MicroSlotSubtype C x ≃ MicroIndexType C x × Fin C.bands.r₀ where
  toFun s :=
    (⟨s.val.1.val, by
      have hlow : C.micro ≤ s.val.1.val := (Finset.mem_filter.mp s.property).2
      have hhigh : s.val.1.val < C.bands.last x + 1 := s.val.1.isLt
      exact Finset.mem_Ico.mpr ⟨by omega, hhigh⟩⟩,
      s.val.2)
  invFun q :=
    ⟨(⟨q.1.val, by
        have hhigh := (Finset.mem_Ico.mp q.1.property).2
        omega⟩, q.2),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_Ico.mp q.1.property).1⟩⟩
  left_inv s := by
    apply Subtype.ext
    rcases s with ⟨⟨⟨j, hj⟩, r⟩, hs⟩
    rfl
  right_inv q := by
    rcases q with ⟨⟨j, hj⟩, r⟩
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

theorem microSlot_exponent_sum (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (hratio : C.bands.ratio = 2) :
    (∑ s : MicroSlotSubtype C x,
      C.bands.c₂ * C.bands.scale x s.val.1.val) =
      (C.bands.r₀ : ℝ) * C.bands.c₂ * C.bands.s' *
        Erdos821.Blueprint.Analytic.L x *
        (∑ j ∈ Finset.Ico C.micro (C.bands.last x + 1), (1 / (2 : ℝ) ^ j)) := by
  classical
  let e := microSlotIndexEquiv C x
  calc
    (∑ s : MicroSlotSubtype C x,
        C.bands.c₂ * C.bands.scale x s.val.1.val) =
      ∑ q : MicroIndexType C x × Fin C.bands.r₀,
        C.bands.c₂ * C.bands.scale x q.1.val := by
          exact Fintype.sum_equiv e
            (fun s => C.bands.c₂ * C.bands.scale x s.val.1.val)
            (fun q => C.bands.c₂ * C.bands.scale x q.1.val)
            (by intro s; rfl)
    _ = ∑ j : MicroIndexType C x, ∑ i : Fin C.bands.r₀,
          C.bands.c₂ * C.bands.scale x j.val := by
      rw [Fintype.sum_prod_type]
    _ = ∑ j : MicroIndexType C x,
          (C.bands.r₀ : ℝ) * (C.bands.c₂ * C.bands.scale x j.val) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
    _ = (C.bands.r₀ : ℝ) * C.bands.c₂ * C.bands.s' *
          Erdos821.Blueprint.Analytic.L x *
          (∑ j : MicroIndexType C x, (1 / (2 : ℝ) ^ j.val)) := by
      simp_rw [Erdos821.Blueprint.BandData.scale, hratio]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hpow : (2 : ℝ) ^ j.val ≠ 0 := by positivity
      field_simp [hpow]
      <;> ring
    _ = _ := by
      change (C.bands.r₀ : ℝ) * C.bands.c₂ * C.bands.s' *
          Erdos821.Blueprint.Analytic.L x *
          (∑ j : {j : ℕ // j ∈ Finset.Ico C.micro (C.bands.last x + 1)},
            (1 / (2 : ℝ) ^ j.val)) = _
      congr 1
      exact Finset.sum_coe_sort
        (Finset.Ico C.micro (C.bands.last x + 1))
        (fun j : ℕ => (1 / (2 : ℝ) ^ j))

theorem microSlot_exponent_sum_le (C : Erdos821.Blueprint.CandidateData)
    (x : ℝ) (hvalid : C.bands.Valid) (hratio : C.bands.ratio = 2)
    (htail : 2 * (C.bands.r₀ : ℝ) * C.bands.c₂ * C.bands.s' /
      (2 : ℝ) ^ C.micro ≤ 1 / 25)
    (hL : 0 ≤ Erdos821.Blueprint.Analytic.L x) :
    (∑ s : MicroSlotSubtype C x,
      C.bands.c₂ * C.bands.scale x s.val.1.val) ≤
      Erdos821.Blueprint.Analytic.L x / 25 := by
  rw [microSlot_exponent_sum C x hratio]
  have hgeom0 := geom_sum_Ico_le_of_lt_one
    (x := (1 / 2 : ℝ)) (m := C.micro) (n := C.bands.last x + 1)
    (by norm_num) (by norm_num)
  have hgeom :
      (∑ j ∈ Finset.Ico C.micro (C.bands.last x + 1), (1 / (2 : ℝ) ^ j)) ≤
        2 * (1 / (2 : ℝ) ^ C.micro) := by
    calc
      (∑ j ∈ Finset.Ico C.micro (C.bands.last x + 1), (1 / (2 : ℝ) ^ j)) =
          ∑ j ∈ Finset.Ico C.micro (C.bands.last x + 1), (1 / 2 : ℝ) ^ j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [div_eq_mul_inv, inv_pow]
      _ ≤ (1 / 2 : ℝ) ^ C.micro / (1 - 1 / 2 : ℝ) := hgeom0
      _ = 2 * (1 / (2 : ℝ) ^ C.micro) := by
        field_simp
        rw [← mul_pow]
        norm_num
  have hcoeff : 0 ≤ (C.bands.r₀ : ℝ) * C.bands.c₂ * C.bands.s' *
      Erdos821.Blueprint.Analytic.L x := by
    rcases hvalid with ⟨hr₀, hc₁, hc₁₂, hs', hratio', hsmall, hvalidTail⟩
    have hr₀R : (0 : ℝ) ≤ C.bands.r₀ := by exact_mod_cast (Nat.zero_le C.bands.r₀)
    have hc₂ : 0 < C.bands.c₂ := hc₁.trans hc₁₂
    exact mul_nonneg (mul_nonneg (mul_nonneg hr₀R hc₂.le) hs'.le) hL
  calc
    _ ≤ (C.bands.r₀ : ℝ) * C.bands.c₂ * C.bands.s' *
        Erdos821.Blueprint.Analytic.L x * (2 * (1 / (2 : ℝ) ^ C.micro)) :=
      mul_le_mul_of_nonneg_left hgeom hcoeff
    _ = (2 * (C.bands.r₀ : ℝ) * C.bands.c₂ * C.bands.s' /
          (2 : ℝ) ^ C.micro) * Erdos821.Blueprint.Analytic.L x := by
      field_simp
      <;> ring
    _ ≤ Erdos821.Blueprint.Analytic.L x / 25 := by
      calc
        _ ≤ (1 / 25 : ℝ) * Erdos821.Blueprint.Analytic.L x :=
          mul_le_mul_of_nonneg_right htail hL
        _ = Erdos821.Blueprint.Analytic.L x / 25 := by ring

theorem microAssignmentProduct_le_x_rpow
    (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ)
    (hvalid : C.bands.Valid) (hratio : C.bands.ratio = 2)
    (htail : 2 * (C.bands.r₀ : ℝ) * C.bands.c₂ * C.bands.s' /
      (2 : ℝ) ^ C.micro ≤ 1 / 25)
    (hx : 1 < x) (m : MicroAssignments C x jstar) :
    (microAssignmentProduct C x jstar m : ℝ) ≤ x ^ (1 / 25 : ℝ) := by
  have hL : 0 ≤ Erdos821.Blueprint.Analytic.L x := by
    dsimp [Erdos821.Blueprint.Analytic.L]
    exact Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)
  have hprodCast : (microAssignmentProduct C x jstar m : ℝ) =
      ∏ s : MicroSlotSubtype C x, ((m s).val : ℝ) := by
    simp [microAssignmentProduct, Nat.cast_prod]
  have hprod : (∏ s : MicroSlotSubtype C x, ((m s).val : ℝ)) ≤
      ∏ s : MicroSlotSubtype C x,
        Real.exp (C.bands.c₂ * C.bands.scale x s.val.1.val) := by
    apply Finset.prod_le_prod₀
    · intro s hs
      exact Nat.cast_nonneg _
    · intro s hs
      exact slotValue_le_bandUpper C x jstar s.val (m s)
  have hsum := microSlot_exponent_sum_le C x hvalid hratio htail hL
  calc
    (microAssignmentProduct C x jstar m : ℝ) =
        ∏ s : MicroSlotSubtype C x, ((m s).val : ℝ) := hprodCast
    _ ≤ ∏ s : MicroSlotSubtype C x,
        Real.exp (C.bands.c₂ * C.bands.scale x s.val.1.val) := hprod
    _ = Real.exp (∑ s : MicroSlotSubtype C x,
        C.bands.c₂ * C.bands.scale x s.val.1.val) := by rw [← Real.exp_sum]
    _ ≤ Real.exp (Erdos821.Blueprint.Analytic.L x / 25) :=
      Real.exp_le_exp.mpr hsum
    _ = x ^ (1 / 25 : ℝ) := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
      congr 1
      dsimp [Erdos821.Blueprint.Analytic.L]
      ring

theorem markProduct_le_exp_groupSize
    (P : Erdos821.Blueprint.Analytic.Geometry)
    (G : Erdos821.Blueprint.Analytic.PrimeGroups) (x : ℝ) (u : ℕ)
    (hAdm : Erdos821.Blueprint.Analytic.Admissible P x G)
    (hL : 1 ≤ Erdos821.Blueprint.Analytic.L x)
    (hb : P.b = 1 / 5) (hd : P.d = 2 / 5)
    (marks : MarkChoices G u) :
    (markProduct G u marks : ℝ) ≤
      Real.exp ((G.size : ℝ) * Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ)) := by
  classical
  rcases hAdm with ⟨hsmallCount, hbigCount, hmass, hprime, hinterval⟩
  have hbound (g : Fin G.size) :
      ((marks g).val : ℝ) ≤ Real.exp (Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ)) := by
    have hgroup := (Finset.mem_filter.mp (marks g).property).1
    have hprime' := hprime g (marks g).val hgroup
    by_cases hg : g ∈ G.small
    · rw [if_pos hg] at hprime'
      have hup : ((marks g).val : ℝ) ≤ Real.exp (Erdos821.Blueprint.Analytic.L x ^ P.b) :=
        hprime'.2
      have hpow : Erdos821.Blueprint.Analytic.L x ^ P.b ≤
          Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) := by
        rw [hb]
        exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      exact hup.trans (Real.exp_le_exp.mpr hpow)
    · rw [if_neg hg] at hprime'
      simpa [hd] using hprime'.2
  have hprod : (markProduct G u marks : ℝ) ≤
      ∏ g : Fin G.size, Real.exp (Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ)) := by
    rw [markProduct, Nat.cast_prod]
    apply Finset.prod_le_prod₀
    · intro g hg
      exact Nat.cast_nonneg _
    · intro g hg
      exact hbound g
  calc
    (markProduct G u marks : ℝ) ≤
        ∏ g : Fin G.size, Real.exp (Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ)) := hprod
    _ = Real.exp ((G.size : ℝ) *
          Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ)) := by
      simp [Finset.prod_const, Real.exp_nat_mul, mul_comm]

theorem groupSize_le_two_C0_T
    (P : Erdos821.Blueprint.Analytic.Geometry)
    (G : Erdos821.Blueprint.Analytic.PrimeGroups) (x : ℝ)
    (hAdm : Erdos821.Blueprint.Analytic.Admissible P x G) :
    (G.size : ℝ) ≤ 2 * P.C₀ * Erdos821.Blueprint.Analytic.T x := by
  classical
  rcases hAdm with ⟨hsmall, hbig, hmass, hprime, hinterval⟩
  have hdisj : Disjoint G.small G.big := by
    refine Finset.disjoint_left.mpr ?_
    intro g hg hgb
    exact (Finset.mem_sdiff.mp hgb).2 hg
  have hunion : G.small ∪ G.big = Finset.univ := by
    ext g
    simp [Erdos821.Blueprint.Analytic.PrimeGroups.big]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  have hsize : G.size = G.small.card + G.big.card := by
    simpa using hcard
  have hsizeR : (G.size : ℝ) = G.small.card + G.big.card := by
    exact_mod_cast hsize
  rcases hsmall with ⟨hsmallLo, hsmallHi⟩
  rcases hbig with ⟨hbigLo, hbigHi⟩
  have hs : (G.small.card : ℝ) ≤ P.C₀ * Erdos821.Blueprint.Analytic.T x := hsmallHi
  have hb : (G.big.card : ℝ) ≤ P.C₀ * Erdos821.Blueprint.Analytic.T x := hbigHi
  rw [hsizeR]
  linarith

theorem markProduct_le_x_half
    (P : Erdos821.Blueprint.Analytic.Geometry)
    (G : Erdos821.Blueprint.Analytic.PrimeGroups) (x : ℝ) (u : ℕ)
    (hAdm : Erdos821.Blueprint.Analytic.Admissible P x G)
    (hL : 1 ≤ Erdos821.Blueprint.Analytic.L x)
    (hLpow : 40 * P.C₀ ≤ Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ))
    (hb : P.b = 1 / 5) (hd : P.d = 2 / 5) (hx : 1 < x)
    (marks : MarkChoices G u) :
    (markProduct G u marks : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
  have hC0 : 0 ≤ P.C₀ := P.positive.2.1.le
  have hlogL : 1 ≤ Real.log x := by
    simpa [Erdos821.Blueprint.Analytic.L] using hL
  have hlog : Erdos821.Blueprint.Analytic.T x ≤
      10 * Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) := by
    dsimp [Erdos821.Blueprint.Analytic.T]
    calc
      Real.log (Erdos821.Blueprint.Analytic.L x) ≤
          (Erdos821.Blueprint.Analytic.L x) ^ (1 / 10 : ℝ) / (1 / 10 : ℝ) :=
        Real.log_le_rpow_div (x := Erdos821.Blueprint.Analytic.L x)
          (by linarith) (ε := (1 / 10 : ℝ)) (by norm_num)
      _ = 10 * Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) := by
        field_simp
        <;> ring
  have hsmallPow : Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) ≤
      Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hLpos : 0 < Erdos821.Blueprint.Analytic.L x := by linarith
  have hpowSq : Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) *
      Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) =
        Erdos821.Blueprint.Analytic.L x := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hpowMul : Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) *
      Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) =
        Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by
    calc
      _ = Erdos821.Blueprint.Analytic.L x ^ ((1 / 10 : ℝ) + (2 / 5 : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by congr 1 <;> norm_num
  have hpowSq : Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) *
      Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) = Erdos821.Blueprint.Analytic.L x := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hlargePow : 40 * P.C₀ ≤ Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) :=
    hLpow.trans hsmallPow
  have hexp : (G.size : ℝ) * Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) ≤
      Erdos821.Blueprint.Analytic.L x / 2 := by
    have hsize := groupSize_le_two_C0_T P G x hAdm
    have hbound : (G.size : ℝ) * Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) ≤
        20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by
      calc
        _ ≤ (2 * P.C₀ * Erdos821.Blueprint.Analytic.T x) *
            Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right hsize (Real.rpow_nonneg (by linarith) _)
        _ ≤ (2 * P.C₀ * (10 * Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ))) *
            Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) hC0))
            (Real.rpow_nonneg (by linarith) _)
        _ = 20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by
          calc
            (2 * P.C₀ * (10 * Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ))) *
                Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) =
              20 * P.C₀ * (Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) *
                Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ)) := by ring
            _ = 20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by
              rw [hpowMul]
    calc
      _ ≤ 20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := hbound
      _ ≤ Erdos821.Blueprint.Analytic.L x / 2 := by
        calc
          20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) =
              (40 * P.C₀) * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) / 2 := by ring
          _ ≤ Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) *
                Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) / 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hlargePow (Real.rpow_nonneg (by linarith) _))
              (by norm_num)
          _ = Erdos821.Blueprint.Analytic.L x / 2 := by rw [hpowSq]
  have hexpMark := markProduct_le_exp_groupSize P G x u hAdm hL hb hd marks
  have hmarkExp : (markProduct G u marks : ℝ) ≤
      Real.exp (Erdos821.Blueprint.Analytic.L x / 2) :=
    hexpMark.trans (Real.exp_le_exp.mpr hexp)
  calc
    (markProduct G u marks : ℝ) ≤
        Real.exp (Erdos821.Blueprint.Analytic.L x / 2) := hmarkExp
    _ = x ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
      congr 1
      dsimp [Erdos821.Blueprint.Analytic.L]
      ring

theorem candidate_micro_mark_product_le_x_three_fifths
    (C : Erdos821.Blueprint.CandidateData) (δ x : ℝ) (jstar u : ℕ)
    (hC : C.Geometry δ)
    (hAdm : Erdos821.Blueprint.Analytic.Admissible C.bands.geometry x
      (C.bands.groups x))
    (hx : 1 < x) (hL : 1 ≤ Erdos821.Blueprint.Analytic.L x)
    (hLpow : 40 * C.bands.geometry.C₀ ≤
      Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ))
    (m : MicroAssignments C x jstar) (marks : MarkChoices (C.bands.groups x) u) :
    ((microAssignmentProduct C x jstar m * markProduct (C.bands.groups x) u marks : ℕ) : ℝ) ≤
      x ^ (3 / 5 : ℝ) := by
  rcases hC with ⟨hvalid, hc₁, hc₂, hratio, hs', hδ, hlast, hprefix, hgap,
    hq, hell, ha, hb, hc, hd, hmicro, hlo, hhi, htheta, htailBound, htail,
    hpsiSmooth, hpsiSupport, hpsiNonneg, hpsiPositive⟩
  have hmicro := microAssignmentProduct_le_x_rpow C x jstar hvalid hratio htailBound hx m
  have hmark := markProduct_le_x_half C.bands.geometry (C.bands.groups x) x u
    hAdm hL hLpow hb hd hx marks
  have hxpos : 0 < x := by linarith
  have hprodNat :
      ((microAssignmentProduct C x jstar m *
        markProduct (C.bands.groups x) u marks : ℕ) : ℝ) =
        (microAssignmentProduct C x jstar m : ℝ) *
          (markProduct (C.bands.groups x) u marks : ℝ) := by simp
  calc
    ((microAssignmentProduct C x jstar m *
        markProduct (C.bands.groups x) u marks : ℕ) : ℝ) =
        (microAssignmentProduct C x jstar m : ℝ) *
          (markProduct (C.bands.groups x) u marks : ℝ) := hprodNat
    _ ≤ x ^ (1 / 25 : ℝ) * x ^ (1 / 2 : ℝ) :=
      mul_le_mul hmicro hmark (Nat.cast_nonneg _) (Real.rpow_nonneg hxpos.le _)
    _ = x ^ ((1 / 25 : ℝ) + (1 / 2 : ℝ)) :=
      (Real.rpow_add hxpos _ _).symm
    _ ≤ x ^ (3 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)




theorem markProduct_le_x_rpow_epsilon
    (P : Erdos821.Blueprint.Analytic.Geometry)
    (G : Erdos821.Blueprint.Analytic.PrimeGroups) (x : ℝ) (u : ℕ)
    (hAdm : Erdos821.Blueprint.Analytic.Admissible P x G)
    (hL : 1 ≤ Erdos821.Blueprint.Analytic.L x)
    (ε : ℝ) (hε : 0 < ε)
    (hLbig : 20 * P.C₀ ≤ ε * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ))
    (hb : P.b = 1 / 5) (hd : P.d = 2 / 5) (hx : 1 < x)
    (marks : MarkChoices G u) :
    (markProduct G u marks : ℝ) ≤ x ^ ε := by
  have hC₀ : 0 ≤ P.C₀ := P.positive.2.1.le
  have hlogL : 1 ≤ Real.log x := by
    simpa [Erdos821.Blueprint.Analytic.L] using hL
  have hlog : Erdos821.Blueprint.Analytic.T x ≤
      10 * Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) := by
    dsimp [Erdos821.Blueprint.Analytic.T]
    calc
      Real.log (Erdos821.Blueprint.Analytic.L x) ≤
          Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) / (1 / 10 : ℝ) :=
        Real.log_le_rpow_div (x := Erdos821.Blueprint.Analytic.L x)
          (by linarith) (ε := (1 / 10 : ℝ)) (by norm_num)
      _ = 10 * Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) := by
        field_simp
        <;> ring
  have hLpos : 0 < Erdos821.Blueprint.Analytic.L x := by linarith
  have hpowMul : Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) *
      Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) =
        Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by
    calc
      _ = Erdos821.Blueprint.Analytic.L x ^ ((1 / 10 : ℝ) + (2 / 5 : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by congr 1 <;> norm_num
  have hpowSq : Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) *
      Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) =
        Erdos821.Blueprint.Analytic.L x := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hsize := groupSize_le_two_C0_T P G x hAdm
  have hbound : (G.size : ℝ) * Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) ≤
      20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 * P.C₀ * Erdos821.Blueprint.Analytic.T x) *
          Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hsize (Real.rpow_nonneg (by linarith) _)
      _ ≤ (2 * P.C₀ * (10 * Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ))) *
          Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) hC₀))
          (Real.rpow_nonneg (by linarith) _)
      _ = 20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by
        calc
          (2 * P.C₀ * (10 * Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ))) *
              Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) =
            20 * P.C₀ * (Erdos821.Blueprint.Analytic.L x ^ (1 / 10 : ℝ) *
              Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ)) := by ring
          _ = 20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := by
            rw [hpowMul]
  have hexp : (G.size : ℝ) * Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ) ≤
      ε * Erdos821.Blueprint.Analytic.L x := by
    calc
      _ ≤ 20 * P.C₀ * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) := hbound
      _ ≤ (ε * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ)) *
            Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hLbig (Real.rpow_nonneg (by linarith) _)
      _ = ε * Erdos821.Blueprint.Analytic.L x := by
        calc
          (ε * Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ)) *
              Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) =
            ε * (Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ) *
              Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ)) := by ring
          _ = ε * Erdos821.Blueprint.Analytic.L x := by rw [hpowSq]
  have hmark := markProduct_le_exp_groupSize P G x u hAdm hL hb hd marks
  calc
    (markProduct G u marks : ℝ) ≤
        Real.exp ((G.size : ℝ) * Erdos821.Blueprint.Analytic.L x ^ (2 / 5 : ℝ)) := hmark
    _ ≤ Real.exp (ε * Erdos821.Blueprint.Analytic.L x) := Real.exp_le_exp.mpr hexp
    _ = x ^ ε := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
      congr 1
      dsimp [Erdos821.Blueprint.Analytic.L]
      ring


theorem candidate_micro_mark_product_le_x_one_twentieth
    (C : Erdos821.Blueprint.CandidateData) (δ x : ℝ) (jstar u : ℕ)
    (hC : C.Geometry δ)
    (hAdm : Erdos821.Blueprint.Analytic.Admissible C.bands.geometry x
      (C.bands.groups x))
    (hx : 1 < x) (hL : 1 ≤ Erdos821.Blueprint.Analytic.L x)
    (hLpow : 2000 * C.bands.geometry.C₀ ≤
      Erdos821.Blueprint.Analytic.L x ^ (1 / 2 : ℝ))
    (m : MicroAssignments C x jstar) (marks : MarkChoices (C.bands.groups x) u) :
    ((microAssignmentProduct C x jstar m * markProduct (C.bands.groups x) u marks : ℕ) : ℝ) ≤
      x ^ (1 / 20 : ℝ) := by
  rcases hC with ⟨hvalid, hc₁, hc₂, hratio, hs', hδ, hlast, hprefix, hgap,
    hq, hell, ha, hb, hc, hd, hmicro, hlo, hhi, htheta, hsmall, htail,
    hpsiSmooth, hpsiSupport, hpsiNonneg, hpsiPositive⟩
  have hmicro := microAssignmentProduct_le_x_rpow C x jstar hvalid hratio hsmall hx m
  have hmark := markProduct_le_x_rpow_epsilon C.bands.geometry (C.bands.groups x)
    x u hAdm hL (1 / 100 : ℝ) (by norm_num)
    (by nlinarith [hLpow]) hb hd hx marks
  have hxpos : 0 < x := by linarith
  have hprodNat :
      ((microAssignmentProduct C x jstar m *
        markProduct (C.bands.groups x) u marks : ℕ) : ℝ) =
        (microAssignmentProduct C x jstar m : ℝ) *
          (markProduct (C.bands.groups x) u marks : ℝ) := by simp
  calc
    ((microAssignmentProduct C x jstar m *
        markProduct (C.bands.groups x) u marks : ℕ) : ℝ) =
        (microAssignmentProduct C x jstar m : ℝ) *
          (markProduct (C.bands.groups x) u marks : ℝ) := hprodNat
    _ ≤ x ^ (1 / 25 : ℝ) * x ^ (1 / 100 : ℝ) :=
      mul_le_mul hmicro hmark (Nat.cast_nonneg _) (Real.rpow_nonneg hxpos.le _)
    _ = x ^ ((1 / 25 : ℝ) + (1 / 100 : ℝ)) :=
      (Real.rpow_add hxpos _ _).symm
    _ ≤ x ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)





theorem sieveProduct_pos (y : ℝ) : 0 < Erdos821.Blueprint.sieveProduct y := by
  classical
  unfold Erdos821.Blueprint.sieveProduct
  apply Finset.prod_pos
  intro p hp
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  have hpcast : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_le
  have hrec : 1 / (p : ℝ) < 1 := by
    calc
      1 / (p : ℝ) < 1 / (1 : ℝ) :=
        one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hpgt
      _ = 1 := by norm_num
  exact sub_pos.mpr (by simpa [one_div] using hrec)

theorem fixed_band_sieveProduct_ratio
    (B : Erdos821.Blueprint.BandData) (j : ℕ) (hvalid : B.Valid)
    (hratio : B.ratio = 2) (hc₁ : B.c₁ = 1) (hc₂ : B.c₂ = 6 / 5)
    (hM : Tendsto (fun y : ℝ => Real.log y * Erdos821.Blueprint.sieveProduct y)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant)))) :
    Tendsto (fun x : ℝ =>
      Erdos821.Blueprint.sieveProduct (Real.exp (B.c₂ * B.scale x j)) /
        Erdos821.Blueprint.sieveProduct (Real.exp (B.c₁ * B.scale x j)))
      atTop (nhds (5 / 6 : ℝ)) := by
  classical
  rcases hvalid with ⟨hr₀, hc₁pos, hc₁₂, hs', hrat, hsmall, hvalidTail⟩
  let ylo : ℝ → ℝ := fun x => Real.exp (B.c₁ * B.scale x j)
  let yhi : ℝ → ℝ := fun x => Real.exp (B.c₂ * B.scale x j)
  have hL : Tendsto (fun x : ℝ => Erdos821.Blueprint.Analytic.L x) atTop atTop := by
    simpa [Erdos821.Blueprint.Analytic.L] using Real.tendsto_log_atTop
  have hcoef : 0 < B.s' / (2 : ℝ) ^ j := div_pos hs' (by positivity)
  have hscaleEq : (fun x : ℝ => B.scale x j) =
      fun x => (B.s' / (2 : ℝ) ^ j) * Erdos821.Blueprint.Analytic.L x := by
    funext x
    simp [Erdos821.Blueprint.BandData.scale, hratio,
      Erdos821.Blueprint.Analytic.L]
    <;> ring
  have hscale : Tendsto (fun x : ℝ => B.scale x j) atTop atTop := by
    have hmul := (tendsto_const_mul_atTop_of_pos hcoef).2 hL
    exact hmul.congr' (Filter.EventuallyEq.of_eq hscaleEq.symm)
  have hloarg : Tendsto (fun x : ℝ => B.c₁ * B.scale x j) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc₁pos).2 hscale
  have hhiarg : Tendsto (fun x : ℝ => B.c₂ * B.scale x j) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (hc₁pos.trans hc₁₂)).2 hscale
  have hylo : Tendsto ylo atTop atTop := by
    change Tendsto (fun x => Real.exp (B.c₁ * B.scale x j)) atTop atTop
    exact Real.tendsto_exp_atTop.comp hloarg
  have hyhi : Tendsto yhi atTop atTop := by
    change Tendsto (fun x => Real.exp (B.c₂ * B.scale x j)) atTop atTop
    exact Real.tendsto_exp_atTop.comp hhiarg
  have hmlo : Tendsto (fun x =>
      Real.log (ylo x) * Erdos821.Blueprint.sieveProduct (ylo x))
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    convert hM.comp hylo using 1 <;> rfl
  have hmhi : Tendsto (fun x =>
      Real.log (yhi x) * Erdos821.Blueprint.sieveProduct (yhi x))
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    convert hM.comp hyhi using 1 <;> rfl
  have hcM : Real.exp (-Real.eulerMascheroniConstant) ≠ 0 :=
    (Real.exp_ne_zero _)
  have hquot0 := hmhi.div hmlo hcM
  have hquot : Tendsto (fun x =>
      (Real.log (yhi x) * Erdos821.Blueprint.sieveProduct (yhi x)) /
        (Real.log (ylo x) * Erdos821.Blueprint.sieveProduct (ylo x)))
      atTop (nhds 1) := by
    convert hquot0 using 1 <;> simp [hcM]
  have hscalePos : ∀ᶠ x : ℝ in atTop, 0 < B.scale x j := by
    filter_upwards [hscale.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    exact hx
  have hratioEq : (fun x =>
      Erdos821.Blueprint.sieveProduct (yhi x) /
        Erdos821.Blueprint.sieveProduct (ylo x)) =ᶠ[atTop]
      fun x => (B.c₁ / B.c₂) *
        ((Real.log (yhi x) * Erdos821.Blueprint.sieveProduct (yhi x)) /
          (Real.log (ylo x) * Erdos821.Blueprint.sieveProduct (ylo x))) := by
    filter_upwards [hscalePos] with x hx
    have hlogLo : Real.log (ylo x) = B.c₁ * B.scale x j := by
      simp [ylo, Real.log_exp]
    have hlogHi : Real.log (yhi x) = B.c₂ * B.scale x j := by
      simp [yhi, Real.log_exp]
    have hVlo : Erdos821.Blueprint.sieveProduct (ylo x) ≠ 0 :=
      ne_of_gt (sieveProduct_pos (ylo x))
    have hVhi : Erdos821.Blueprint.sieveProduct (yhi x) ≠ 0 :=
      ne_of_gt (sieveProduct_pos (yhi x))
    rw [hlogLo, hlogHi]
    field_simp [ne_of_gt hx, hc₁pos.ne', (hc₁pos.trans hc₁₂).ne', hVlo, hVhi]
    <;> ring
  have hcombo : Tendsto (fun x => (B.c₁ / B.c₂) *
      ((Real.log (yhi x) * Erdos821.Blueprint.sieveProduct (yhi x)) /
        (Real.log (ylo x) * Erdos821.Blueprint.sieveProduct (ylo x))))
      atTop (nhds (B.c₁ / B.c₂)) := by
    simpa using tendsto_const_nhds.mul hquot
  have hratioLimit := hcombo.congr' hratioEq.symm
  simpa [ylo, yhi, hc₁, hc₂] using hratioLimit

theorem fixed_band_reciprocal_sum_lower
    (B : Erdos821.Blueprint.BandData) (j : ℕ) (hvalid : B.Valid)
    (hratio : B.ratio = 2) (hc₁ : B.c₁ = 1) (hc₂ : B.c₂ = 6 / 5)
    (hM : Tendsto (fun y : ℝ => Real.log y * Erdos821.Blueprint.sieveProduct y)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant)))) :
    ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ B.band x j, (p : ℝ)⁻¹) ≥ 1 / 12 := by
  have hratioLimit := fixed_band_sieveProduct_ratio B j hvalid hratio hc₁ hc₂ hM
  have hratioEventually : ∀ᶠ x : ℝ in atTop,
      Erdos821.Blueprint.sieveProduct (Real.exp (B.c₂ * B.scale x j)) /
        Erdos821.Blueprint.sieveProduct (Real.exp (B.c₁ * B.scale x j)) < 11 / 12 := by
    exact hratioLimit.eventually (Iio_mem_nhds (by norm_num : (5 / 6 : ℝ) < 11 / 12))
  have hxEventually : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  filter_upwards [hratioEventually, hxEventually] with x hratioX hx
  let ylo := Real.exp (B.c₁ * B.scale x j)
  let yhi := Real.exp (B.c₂ * B.scale x j)
  let Qlo := Erdos821.Blueprint.primesUpTo ylo
  let Qhi := Erdos821.Blueprint.primesUpTo yhi
  let diff := Qhi \ Qlo
  have hscale : 0 < B.scale x j := by
    have hL : 0 < Erdos821.Blueprint.Analytic.L x :=
      Real.log_pos hx
    rcases hvalid with ⟨hr₀, hc₁pos, hc₁₂, hs', _, _, _⟩
    rw [Erdos821.Blueprint.BandData.scale, hratio]
    exact div_pos (mul_pos hs' hL) (by positivity)
  have hya : 0 ≤ ylo := (Real.exp_pos _).le
  have hyb : 0 ≤ yhi := (Real.exp_pos _).le
  have hylohi : ylo ≤ yhi := by
    apply Real.exp_le_exp.mpr
    nlinarith [hc₁, hc₂, hscale]
  have hQsub : Qlo ⊆ Qhi :=
    Erdos821.P9Core.primesUpTo_mono hylohi hya hyb
  have hdiffBand : diff ⊆ B.band x j := by
    intro p hp
    have hpmem := Finset.mem_sdiff.mp hp
    have hprime : p.Prime :=
      (Erdos821.P9Core.mem_primesUpTo_iff yhi hyb p).1 hpmem.1 |>.1
    have hupper : (p : ℝ) ≤ yhi :=
      (Erdos821.P9Core.mem_primesUpTo_iff yhi hyb p).1 hpmem.1 |>.2
    have hnotlo : ¬ (p : ℝ) ≤ ylo := by
      intro h
      exact hpmem.2 ((Erdos821.P9Core.mem_primesUpTo_iff ylo hya p).2 ⟨hprime, h⟩)
    have hlo : ⌈ylo⌉₊ ≤ p := Nat.ceil_le.mpr (le_of_lt (not_le.mp hnotlo))
    have hhi : p ≤ ⌊yhi⌋₊ := (Nat.le_floor_iff hyb).mpr hupper
    rw [Erdos821.Blueprint.BandData.band, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hprime⟩
  have hprodBand : (∏ p ∈ B.band x j, (1 - (p : ℝ)⁻¹)) ≤
      ∏ p ∈ diff, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀ hdiffBand
    · intro p hp
      have hprime := (Finset.mem_filter.mp hp).2
      have hpgt : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      have hinv : (p : ℝ)⁻¹ ≤ 1 := by
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (le_of_lt hpgt))
      exact sub_nonneg.mpr hinv
    · intro p hp hnot
      have hprime := (Finset.mem_filter.mp hp).2
      have hpgt : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      have hinv : (p : ℝ)⁻¹ ≤ 1 := by
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (le_of_lt hpgt))
      have hrec0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
      exact sub_le_self 1 hrec0
  have hparts : Erdos821.Blueprint.sieveProduct yhi =
      Erdos821.Blueprint.sieveProduct ylo *
        ∏ p ∈ diff, (1 - (p : ℝ)⁻¹) := by
    have h := (Finset.prod_sdiff (s₁ := Qlo) (s₂ := Qhi)
      (f := fun p : ℕ => 1 - (p : ℝ)⁻¹) hQsub).symm
    dsimp [diff, Qhi, Qlo, Erdos821.Blueprint.sieveProduct] at h ⊢
    calc
      ∏ p ∈ Qhi, (1 - (p : ℝ)⁻¹) =
          (∏ p ∈ diff, (1 - (p : ℝ)⁻¹)) *
            ∏ p ∈ Qlo, (1 - (p : ℝ)⁻¹) := h
      _ = (∏ p ∈ Qlo, (1 - (p : ℝ)⁻¹)) *
            ∏ p ∈ diff, (1 - (p : ℝ)⁻¹) := by ac_rfl
  have hdiffEq : (∏ p ∈ diff, (1 - (p : ℝ)⁻¹)) =
      Erdos821.Blueprint.sieveProduct yhi / Erdos821.Blueprint.sieveProduct ylo := by
    rw [hparts]
    field_simp [ne_of_gt (sieveProduct_pos ylo)]
  have hbandProd :
      (∏ p ∈ B.band x j, (1 - (p : ℝ)⁻¹)) ≤ 11 / 12 := by
    calc
      (∏ p ∈ B.band x j, (1 - (p : ℝ)⁻¹)) ≤
          ∏ p ∈ diff, (1 - (p : ℝ)⁻¹) := hprodBand
      _ = Erdos821.Blueprint.sieveProduct yhi /
            Erdos821.Blueprint.sieveProduct ylo := hdiffEq
      _ ≤ 11 / 12 := hratioX.le
  have hsum := one_sub_product_le_sum (s := B.band x j)
      (fun p => (p : ℝ)⁻¹)
      (by
        intro p hp
        have hprime := (Finset.mem_filter.mp hp).2
        exact inv_nonneg.mpr (Nat.cast_nonneg _))
      (by
        intro p hp
        have hprime := (Finset.mem_filter.mp hp).2
        have hpgt : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
        have hinv : (p : ℝ)⁻¹ ≤ 1 := by
          simpa [one_div] using
            (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (le_of_lt hpgt))
        exact hinv)
  linarith

theorem candidate_macro_band_reciprocal_lower_eventually
    (C : Erdos821.Blueprint.CandidateData) (δ : ℝ)
    (hC : C.Geometry δ)
    (hM : Tendsto (fun y : ℝ => Real.log y * Erdos821.Blueprint.sieveProduct y)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant)))) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range C.micro,
      (∑ p ∈ C.bands.band x j, (p : ℝ)⁻¹) ≥ 1 / 12 := by
  rcases hC with ⟨hvalid, hc₁, hc₂, hratio, hs', hδ, hlast, hprefix, hgap,
    hq, hell, ha, hb, hc, hd, hmicro, hlo, hhi, htheta, hsmall, htail,
    hpsiSmooth, hpsiSupport, hpsiNonneg, hpsiPositive⟩
  rw [Filter.eventually_all_finset]
  intro j hj
  exact fixed_band_reciprocal_sum_lower C.bands j hvalid hratio hc₁ hc₂ hM

def slotReciprocalMass (B : Erdos821.Blueprint.BandData)
    (x : ℝ) (jstar : ℕ) (s : B.Slot x) : ℝ :=
  ∑ v ∈ B.slotValues x jstar s, (v : ℝ)⁻¹

theorem candidate_macro_slot_reciprocal_lower_eventually
    (C : Erdos821.Blueprint.CandidateData) (δ : ℝ) (jstar : ℕ)
    (hC : C.Geometry δ) (hj : C.micro ≤ jstar)
    (hM : Tendsto (fun y : ℝ => Real.log y * Erdos821.Blueprint.sieveProduct y)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant)))) :
    ∀ᶠ x : ℝ in atTop,
      C.micro ≤ C.bands.last x + 1 ∧
        ∀ s : MacroSlotSubtype C x,
          1 / 12 ≤ slotReciprocalMass C.bands x jstar s.val := by
  have hbands := candidate_macro_band_reciprocal_lower_eventually C δ hC hM
  rcases hC with ⟨hvalid, hc₁, hc₂, hratio, hs', hδ, hlast, hprefix, hgap,
    hq, hell, ha, hb, hc, hd, hmicro, hlo, hhi, htheta, hsmall, htail,
    hpsiSmooth, hpsiSupport, hpsiNonneg, hpsiPositive⟩
  have hlastLarge : ∀ᶠ x : ℝ in atTop, C.micro ≤ C.bands.last x := by
    rcases hvalid with ⟨hr₀, hb₁, hb₂, hs'valid, hratio', hsmall', hgapValid, hlast, hvalidTail⟩
    exact hlast.eventually (eventually_ge_atTop C.micro)
  filter_upwards [hlastLarge, hbands] with x hlastx hbandx
  constructor
  · omega
  · intro s
    have hsidx : s.val.1.val < C.micro := (Finset.mem_filter.mp s.property).2
    have hsj : s.val.1.val < jstar := lt_of_lt_of_le hsidx hj
    have hnotSpecial : ¬ (s.val.1.val = jstar ∧ s.val.2.val = 0) := by omega
    have hvalues : C.bands.slotValues x jstar s.val = C.bands.band x s.val.1.val := by
      simp [Erdos821.Blueprint.BandData.slotValues, hnotSpecial]
    have hband := hbandx s.val.1.val (Finset.mem_range.mpr hsidx)
    rw [slotReciprocalMass, hvalues]
    exact hband


theorem slot_reciprocal_subtype_sum_eq
    (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ)
    (s : C.bands.Slot x) :
    (∑ v : C.bands.SlotValue x jstar s, ((v.val : ℝ)⁻¹)) =
      ∑ v ∈ C.bands.slotValues x jstar s, ((v : ℝ)⁻¹) := by
  exact Finset.sum_coe_sort (C.bands.slotValues x jstar s)
    (fun v => ((v : ℝ)⁻¹))

theorem macroSlot_reciprocal_product_lower_eventually
    (C : Erdos821.Blueprint.CandidateData) (δ : ℝ) (jstar : ℕ)
    (hC : C.Geometry δ) (hj : C.micro ≤ jstar)
    (hM : Tendsto (fun y : ℝ => Real.log y * Erdos821.Blueprint.sieveProduct y)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant)))) :
    ∀ᶠ x : ℝ in atTop,
      C.micro ≤ C.bands.last x + 1 ∧
        (1 / (12 : ℝ)) ^ (C.micro * C.bands.r₀) ≤
          ∏ s : MacroSlotSubtype C x,
            ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹) := by
  have hslot := candidate_macro_slot_reciprocal_lower_eventually C δ jstar hC hj hM
  filter_upwards [hslot] with x hx
  rcases hx with ⟨hbound, hlow⟩
  have hcard : Fintype.card (MacroSlotSubtype C x) = Fintype.card (MacroSlotIndex C) :=
    Fintype.card_congr (macroSlotEquiv C x hbound)
  have hcard' : Fintype.card (MacroSlotSubtype C x) = C.micro * C.bands.r₀ := by
    simpa [MacroSlotIndex, Fintype.card_prod] using hcard
  have hprod :
      (∏ s : MacroSlotSubtype C x, (1 / (12 : ℝ))) ≤
        ∏ s : MacroSlotSubtype C x,
          ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹) := by
    apply Finset.prod_le_prod₀
    · intro s hs
      norm_num
    · intro s hs
      rw [slot_reciprocal_subtype_sum_eq]
      exact hlow s
  have hcardFinset : (macroSlots C x).card = C.micro * C.bands.r₀ := by
    simpa [MacroSlotSubtype] using hcard'
  have hconst : (∏ s : MacroSlotSubtype C x, (1 / (12 : ℝ))) =
      (1 / (12 : ℝ)) ^ (C.micro * C.bands.r₀) := by
    simp [Finset.prod_const, hcardFinset]
  exact ⟨hbound, hconst ▸ hprod⟩

theorem slot_reciprocal_product_factorization
    (C : Erdos821.Blueprint.CandidateData) (x : ℝ) (jstar : ℕ) :
    (∏ s : C.bands.Slot x,
      ∑ v ∈ C.bands.slotValues x jstar s, ((v : ℝ)⁻¹)) =
      (∏ s : MicroSlotSubtype C x,
        ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹)) *
      (∏ s : MacroSlotSubtype C x,
        ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹)) := by
  classical
  let f := fun s : C.bands.Slot x =>
    ∑ v ∈ C.bands.slotValues x jstar s, ((v : ℝ)⁻¹)
  have hpart := micro_macro_slots_partition C x
  change (∏ s ∈ Finset.univ, f s) = _
  calc
    (∏ s ∈ Finset.univ, f s) =
        (∏ s ∈ microSlots C x, f s) * (∏ s ∈ macroSlots C x, f s) := by
      rw [← hpart.2, Finset.prod_union hpart.1]
    _ = (∏ s : MicroSlotSubtype C x,
          ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹)) *
        (∏ s : MacroSlotSubtype C x,
          ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹)) := by
      rw [← Finset.prod_coe_sort (microSlots C x) f,
        ← Finset.prod_coe_sort (macroSlots C x) f]
      apply congrArg₂ (· * ·) <;>
        apply Finset.prod_congr rfl <;> intro s hs <;>
        rw [slot_reciprocal_subtype_sum_eq]

theorem normalized_micro_harmonic_le_harmonicQ_eventually
    (C : Erdos821.Blueprint.CandidateData) (δ : ℝ) (jstar : ℕ)
    (hC : C.Geometry δ) (hj : C.micro ≤ jstar)
    (hM : Tendsto (fun y : ℝ => Real.log y * Erdos821.Blueprint.sieveProduct y)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant)))) :
    ∀ᶠ x : ℝ in atTop,
      listNormalizer C.bands x *
          (Fintype.card (MacroSlotIndex C)).factorial *
          (∏ s : MicroSlotSubtype C x,
            ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹)) ≤
        ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) *
          (12 : ℝ) ^ (C.micro * C.bands.r₀) * C.bands.harmonicQ x jstar := by
  have hmacro := macroSlot_reciprocal_product_lower_eventually C δ jstar hC hj hM
  filter_upwards [hmacro] with x hx
  rcases hx with ⟨hbound, hmacroLower⟩
  let microRaw := ∏ s : MicroSlotSubtype C x,
    ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹)
  let macroRaw := ∏ s : MacroSlotSubtype C x,
    ∑ v : C.bands.SlotValue x jstar s.val, ((v.val : ℝ)⁻¹)
  let N := C.micro * C.bands.r₀
  let F : ℝ := (Fintype.card (MacroSlotIndex C)).factorial
  have hfactor :
      (∏ s : C.bands.Slot x,
        ∑ v ∈ C.bands.slotValues x jstar s, ((v : ℝ)⁻¹)) = microRaw * macroRaw := by
    simpa [microRaw, macroRaw] using slot_reciprocal_product_factorization C x jstar
  have hQeq : C.bands.harmonicQ x jstar =
      listNormalizer C.bands x * (microRaw * macroRaw) := by
    calc
      C.bands.harmonicQ x jstar = listNormalizer C.bands x *
          (∏ s : C.bands.Slot x,
            ∑ v ∈ C.bands.slotValues x jstar s, ((v : ℝ)⁻¹)) := by
        simp [Erdos821.Blueprint.BandData.harmonicQ, listNormalizer]
      _ = listNormalizer C.bands x * (microRaw * macroRaw) := by rw [hfactor]
  have hmicro0 : 0 ≤ microRaw := by
    apply Finset.prod_nonneg
    intro s hs
    apply Finset.sum_nonneg
    intro v hv
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hnorm0 : 0 ≤ listNormalizer C.bands x := by
    unfold listNormalizer
    exact inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  have hF0 : 0 ≤ F := by positivity
  have hbase0 : 0 ≤ listNormalizer C.bands x * F * microRaw :=
    mul_nonneg (mul_nonneg hnorm0 hF0) hmicro0
  have hscalar : 1 ≤ (12 : ℝ) ^ N * macroRaw := by
    have hpow : (12 : ℝ) ^ N * (1 / (12 : ℝ)) ^ N = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      1 = (12 : ℝ) ^ N * (1 / (12 : ℝ)) ^ N := hpow.symm
      _ ≤ (12 : ℝ) ^ N * macroRaw :=
        mul_le_mul_of_nonneg_left hmacroLower (pow_nonneg (by norm_num) _)
  have hmain :
      listNormalizer C.bands x * F * microRaw ≤
        (listNormalizer C.bands x * F * microRaw) *
          ((12 : ℝ) ^ N * macroRaw) :=
    le_mul_of_one_le_right hbase0 hscalar
  calc
    listNormalizer C.bands x *
        (Fintype.card (MacroSlotIndex C)).factorial * microRaw =
        listNormalizer C.bands x * F * microRaw := by rfl
    _ ≤ (listNormalizer C.bands x * F * microRaw) *
          ((12 : ℝ) ^ N * macroRaw) := hmain
    _ = F * (12 : ℝ) ^ N * C.bands.harmonicQ x jstar := by
      rw [hQeq]
      dsimp [F, N]
      ring






end

end Erdos821.P9Core
