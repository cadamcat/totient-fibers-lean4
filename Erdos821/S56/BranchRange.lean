import Erdos821.S56.Definitions

namespace Erdos821.S56
open scoped BigOperators

private def remaining {n : ℕ} (v : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin n => i ≤ t.val), v t

private theorem residual_step {n : ℕ} (target : ℝ) (v : Fin n → ℝ)
    (δ : Fin n → Bool) (i : ℕ) (hi : i < n) :
    residual target v δ (i + 1) = residual target v δ i -
      (if δ ⟨i, hi⟩ then v ⟨i, hi⟩ else 0) := by
  classical
  have hset : Finset.univ.filter (fun t : Fin n => t.val < i + 1) =
      insert ⟨i, hi⟩ (Finset.univ.filter (fun t : Fin n => t.val < i)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro ht
      by_cases hti : t.val = i
      · exact Or.inl (Fin.ext hti)
      · exact Or.inr (by omega)
    · rintro (rfl | ht)
      · exact Nat.lt_succ_self i
      · omega
  have hnot : (⟨i, hi⟩ : Fin n) ∉ Finset.univ.filter (fun t : Fin n => t.val < i) := by simp
  simp only [residual, hset, Finset.sum_insert hnot]
  ring

private theorem remaining_step {n : ℕ} (v : Fin n → ℝ) (i : ℕ) (hi : i < n) :
    remaining v i = v ⟨i, hi⟩ + remaining v (i + 1) := by
  classical
  have hset : Finset.univ.filter (fun t : Fin n => i ≤ t.val) =
      insert ⟨i, hi⟩ (Finset.univ.filter (fun t : Fin n => i + 1 ≤ t.val)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro ht
      by_cases hti : t.val = i
      · exact Or.inl (Fin.ext hti)
      · exact Or.inr (by omega)
    · rintro (rfl | ht)
      · exact le_rfl
      · omega
  have hnot : (⟨i, hi⟩ : Fin n) ∉ Finset.univ.filter (fun t : Fin n => i + 1 ≤ t.val) := by simp
  simp only [remaining, hset, Finset.sum_insert hnot]

/-- Every positive branch retains the logarithmic residual invariant at each prefix. -/
theorem _root_.Erdos821.S56Core.branch_prefix_bounds (n : ℕ) (target terminal : ℝ) (v s : Fin n → ℝ) (γ : ℝ → ℝ)
    (ht : 0 ≤ target) (hterm : 0 ≤ terminal) (hinit : target ≤ (∑ i, v i) + terminal)
    (hv : ∀ i, 0 < v i ∧ 0 < s i)
    (hγ : ∀ t, 0 ≤ γ t ∧ γ t ≤ 1 ∧ (t ≤ 0 → γ t = 0) ∧ (1 ≤ t → γ t = 1))
    (hroom : ∀ i, v i + s i ≤
      (∑ t ∈ Finset.univ.filter (fun t : Fin n => i.val < t.val), v t) + terminal) :
    ∀ δ : Fin n → Bool, 0 < branchMass target v s γ δ →
      ∀ i : ℕ, i ≤ n → 0 ≤ residual target v δ i ∧
        residual target v δ i ≤
          (∑ t ∈ Finset.univ.filter (fun t : Fin n => i ≤ t.val), v t) + terminal := by
  classical
  intro δ hmass
  let prob : Fin n → ℝ := fun i =>
    if δ i then γ ((residual target v δ i.val - v i) / s i)
    else 1 - γ ((residual target v δ i.val - v i) / s i)
  have hnonneg (i : Fin n) : 0 ≤ prob i := by
    dsimp [prob]
    split
    · exact (hγ _).1
    · linarith [(hγ ((residual target v δ i.val - v i) / s i)).2.1]
  have hne : ∀ i : Fin n, prob i ≠ 0 := by
    have hp : (∏ i, prob i) ≠ 0 := hmass.ne'
    exact fun i => (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have hpos (i : Fin n) : 0 < prob i := lt_of_le_of_ne (hnonneg i) (hne i).symm
  have hinvariant : ∀ i : ℕ, i ≤ n →
      0 ≤ residual target v δ i ∧ residual target v δ i ≤ remaining v i + terminal := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa [residual, remaining] using And.intro ht hinit
    | succ i ih =>
      intro hi
      have hin : i < n := by omega
      let j : Fin n := ⟨i, hin⟩
      obtain ⟨hR0, hRmax⟩ := ih (by omega)
      have hstep := residual_step target v δ i hin
      have hrem := remaining_step v i hin
      have hs : 0 < s j := (hv j).2
      by_cases hd : δ j = true
      · have hp : 0 < γ ((residual target v δ i - v j) / s j) := by
          simpa [prob, hd, j] using hpos j
        have hRv : v j < residual target v δ i := by
          by_contra hh
          have harg : (residual target v δ i - v j) / s j ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hh)) hs.le
          have hz := (hγ _).2.2.1 harg
          linarith
        have hnew : residual target v δ (i + 1) = residual target v δ i - v j := by
          simpa [j, hd] using hstep
        rw [hnew]
        constructor
        · linarith
        · dsimp [j] at hRv ⊢
          linarith
      · have hfalse : δ j = false := Bool.eq_false_iff.mpr hd
        have hp : 0 < 1 - γ ((residual target v δ i - v j) / s j) := by
          simpa [prob, hfalse, j] using hpos j
        have harg : (residual target v δ i - v j) / s j < 1 := by
          by_contra hh
          have hz := (hγ _).2.2.2 (le_of_not_gt hh)
          linarith
        have hskip : residual target v δ i < v j + s j := by
          have hh := (div_lt_iff₀ hs).mp harg
          linarith
        have hroomj : v j + s j ≤ remaining v (i + 1) + terminal := by
          convert hroom j using 1
          congr 2
        have hnew : residual target v δ (i + 1) = residual target v δ i := by
          simpa [j, hfalse] using hstep
        rw [hnew]
        exact ⟨hR0, le_trans hskip.le hroomj⟩
  simpa [remaining] using hinvariant

/-- Every branch of positive mass ends within the terminal logarithmic allowance. -/
theorem branch_range_proved (n : ℕ) (target terminal : ℝ) (v s : Fin n → ℝ) (γ : ℝ → ℝ)
    (ht : 0 ≤ target) (hterm : 0 ≤ terminal) (hinit : target ≤ (∑ i, v i) + terminal)
    (hv : ∀ i, 0 < v i ∧ 0 < s i)
    (hγ : ∀ t, 0 ≤ γ t ∧ γ t ≤ 1 ∧ (t ≤ 0 → γ t = 0) ∧ (1 ≤ t → γ t = 1))
    (hroom : ∀ i, v i + s i ≤
      (∑ t ∈ Finset.univ.filter (fun t : Fin n => i.val < t.val), v t) + terminal) :
    ∀ δ : Fin n → Bool, 0 < branchMass target v s γ δ →
      0 ≤ residual target v δ n ∧ residual target v δ n ≤ terminal := by
  intro δ hmass
  have h := Erdos821.S56Core.branch_prefix_bounds n target terminal v s γ
    ht hterm hinit hv hγ hroom δ hmass n le_rfl
  have hz : (∑ t ∈ Finset.univ.filter (fun t : Fin n => n ≤ t.val), v t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    exact False.elim (Nat.not_le_of_gt t.isLt (Finset.mem_filter.mp ht).2)
  simpa [hz] using h


end Erdos821.S56
