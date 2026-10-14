import Erdos821.S10.BalancedTasks

/-! Finite-sum bookkeeping for the balanced prime-to-proxy replacements. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace Erdos821.S10Prime
open Erdos821.Blueprint Erdos821.P10 Erdos821.P7Core
attribute [local instance] Classical.propDecidable

/-- The candidate weight attached to an ordered factor pair. -/
def pairKernel (C : CandidateData) (x : ℝ) (jstar m n : ℕ) : ℝ :=
  if Odd (m * n) ∧ 1 < m * n then C.weighted x jstar ((m * n - 1) / 2) else 0

theorem pairKernel_comm (C : CandidateData) (x : ℝ) (jstar m n : ℕ) :
    pairKernel C x jstar m n = pairKernel C x jstar n m := by
  simp [pairKernel, Nat.mul_comm]

theorem pairKernel_nonneg (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (hw : ∀ u : ℕ, 0 ≤ C.weighted x jstar u) (m n : ℕ) :
    0 ≤ pairKernel C x jstar m n := by
  unfold pairKernel
  split_ifs
  · exact hw _
  · exact le_rfl

/-- A nonzero pair kernel comes from a supported shifted integer. -/
theorem pairKernel_ne_zero {C : CandidateData} {x : ℝ} {jstar m n : ℕ}
    (h : pairKernel C x jstar m n ≠ 0) :
    ∃ u : ℕ, m * n = 2 * u + 1 ∧ C.weighted x jstar u ≠ 0 := by
  unfold pairKernel at h
  by_cases hc : Odd (m * n) ∧ 1 < m * n
  · rw [if_pos hc] at h
    obtain ⟨k, hk⟩ := hc.1
    refine ⟨k, hk, ?_⟩
    have hu : (m * n - 1) / 2 = k := by rw [hk]; omega
    rwa [hu] at h
  · rw [if_neg hc] at h
    exact absurd rfl h

/-- Cut a coefficient to a closed real interval. -/
def cut (lo hi : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  if lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi then a n else 0

theorem cut_ne_zero {lo hi : ℝ} {a : ℕ → ℝ} {n : ℕ} (h : cut lo hi a n ≠ 0) :
    lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi := by
  unfold cut at h
  by_contra hn
  rw [if_neg hn] at h
  exact h rfl

theorem cut_sub (lo hi : ℝ) (a b : ℕ → ℝ) (n : ℕ) :
    cut lo hi (fun k => a k - b k) n = cut lo hi a n - cut lo hi b n := by
  unfold cut
  split_ifs <;> simp

/-- The pair sum over the full natural range `[1, 2^K)`. -/
def fullPair (C : CandidateData) (x : ℝ) (jstar K : ℕ) (a b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 (2 ^ K), ∑ n ∈ Finset.Ico 1 (2 ^ K),
    pairKernel C x jstar m n * a m * b n

/-- A natural dyadic box of the pair sum. -/
def pairBox (C : CandidateData) (x : ℝ) (jstar : ℕ) (a b : ℕ → ℝ) (U V : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico U (2 * U), ∑ n ∈ Finset.Ico V (2 * V),
    pairKernel C x jstar m n * a m * b n

/-- A window sum is a cut sum over any natural range `[1, 2^K)` containing it. -/
theorem sum_window_eq (lo hi : ℝ) (K : ℕ) (hlo : 1 ≤ lo) (hhi0 : 0 ≤ hi)
    (hhi : hi < ((2 ^ K : ℕ) : ℝ)) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊, f m =
      ∑ m ∈ Finset.Ico 1 (2 ^ K), cut lo hi f m := by
  unfold cut
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    have hlo' : lo ≤ (m : ℝ) := Nat.ceil_le.1 h1
    have hhi' : (m : ℝ) ≤ hi := (Nat.le_floor_iff hhi0).1 h2
    refine ⟨⟨?_, ?_⟩, hlo', hhi'⟩
    · have : (1 : ℝ) ≤ (m : ℝ) := le_trans hlo hlo'
      exact_mod_cast this
    · have : (m : ℝ) < ((2 ^ K : ℕ) : ℝ) := lt_of_le_of_lt hhi' hhi
      exact_mod_cast this
  · rintro ⟨_, hlo', hhi'⟩
    exact ⟨Nat.ceil_le.2 hlo', (Nat.le_floor_iff hhi0).2 hhi'⟩

/-- A double window sum is the full-range pair sum of cut coefficients. -/
theorem windowPair_eq_fullPair (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (lo hi : ℝ) (a b : ℕ → ℝ) (K : ℕ)
    (hlo : 1 ≤ lo) (hhi0 : 0 ≤ hi) (hhi : hi < ((2 ^ K : ℕ) : ℝ)) :
    (∑ m ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊, ∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
      if Odd (m * n) ∧ 1 < m * n then
        C.weighted x jstar ((m * n - 1) / 2) * a m * b n else 0) =
      fullPair C x jstar K (cut lo hi a) (cut lo hi b) := by
  have hterm : ∀ m n : ℕ,
      (if Odd (m * n) ∧ 1 < m * n then
        C.weighted x jstar ((m * n - 1) / 2) * a m * b n else 0) =
        pairKernel C x jstar m n * a m * b n := by
    intro m n
    unfold pairKernel
    split_ifs <;> simp
  simp_rw [hterm]
  have hinner : ∀ m : ℕ,
      (∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊, pairKernel C x jstar m n * a m * b n) =
        ∑ n ∈ Finset.Ico 1 (2 ^ K),
          cut lo hi (fun n => pairKernel C x jstar m n * a m * b n) n :=
    fun m => sum_window_eq lo hi K hlo hhi0 hhi _
  simp_rw [hinner]
  rw [sum_window_eq lo hi K hlo hhi0 hhi]
  unfold fullPair
  apply Finset.sum_congr rfl
  intro m _
  unfold cut
  by_cases hm : lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi
  · simp only [if_pos hm]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp
  · simp only [if_neg hm]
    simp

/-- The frozen balanced pair mass is the full-range pair sum of cut coefficients. -/
theorem balancedPairWindowMass_eq_fullPair (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (κ : ℝ) (a b : ℕ → ℝ) (K : ℕ)
    (hlo : 1 ≤ x ^ (1 / 2 - 2 * κ)) (hhi0 : 0 ≤ x ^ (1 / 2 + 2 * κ))
    (hhi : x ^ (1 / 2 + 2 * κ) < ((2 ^ K : ℕ) : ℝ)) :
    balancedPairWindowMass C x jstar κ a b =
      fullPair C x jstar K (cut (x ^ (1 / 2 - 2 * κ)) (x ^ (1 / 2 + 2 * κ)) a)
        (cut (x ^ (1 / 2 - 2 * κ)) (x ^ (1 / 2 + 2 * κ)) b) := by
  unfold balancedPairWindowMass balancedWindow
  exact windowPair_eq_fullPair C x jstar _ _ a b K hlo hhi0 hhi

/-- The three-term prime-to-proxy decomposition of a product of prime tests. -/
theorem fullPair_decompose (C : CandidateData) (x : ℝ) (jstar K : ℕ)
    (P p d : ℕ → ℝ) (hd : ∀ n, d n = P n - p n) :
    fullPair C x jstar K P P =
      fullPair C x jstar K d P + fullPair C x jstar K p d + fullPair C x jstar K p p := by
  unfold fullPair
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [hd m, hd n]
  ring

/-- Exchanging the factor roles leaves the pair sum unchanged. -/
theorem fullPair_swap (C : CandidateData) (x : ℝ) (jstar K : ℕ) (a b : ℕ → ℝ) :
    fullPair C x jstar K a b = fullPair C x jstar K b a := by
  unfold fullPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  rw [pairKernel_comm]
  ring

/-- A pointwise majorant of nonnegative coefficients bounds the pair sum. -/
theorem fullPair_le_of_majorant (C : CandidateData) (x : ℝ) (jstar K : ℕ)
    (hw : ∀ u : ℕ, 0 ≤ C.weighted x jstar u) (a r : ℕ → ℝ) (c : ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ c * r n) :
    fullPair C x jstar K a a ≤ c ^ 2 * fullPair C x jstar K r r := by
  unfold fullPair
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have hk := pairKernel_nonneg C x jstar hw m n
  have hmn : a m * a n ≤ (c * r m) * (c * r n) :=
    mul_le_mul (ha m).2 (ha n).2 (ha n).1 (le_trans (ha m).1 (ha m).2)
  have := mul_le_mul_of_nonneg_left hmn hk
  calc pairKernel C x jstar m n * a m * a n
      = pairKernel C x jstar m n * (a m * a n) := by ring
    _ ≤ pairKernel C x jstar m n * ((c * r m) * (c * r n)) := this
    _ = c ^ 2 * (pairKernel C x jstar m n * r m * r n) := by ring

/-- Reindex the full-range pair sum by natural dyadic boxes. -/
theorem fullPair_eq_boxes (C : CandidateData) (x : ℝ) (jstar K : ℕ) (a b : ℕ → ℝ) :
    fullPair C x jstar K a b =
      ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
        pairBox C x jstar a b (2 ^ k) (2 ^ l) := by
  unfold fullPair
  rw [sum_nat_pair_dyadic_boxes K (fun m n => pairKernel C x jstar m n * a m * b n)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  unfold pairBox
  have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hl : 2 ^ (l + 1) = 2 * 2 ^ l := by ring
  rw [hk, hl]

/-- The complex Type II form with real coefficients is the real dyadic box. -/
theorem typeIISum_eq_pairBox (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (a b : ℕ → ℝ) (U V : ℕ) :
    typeIISum C.bands x jstar (U : ℝ) (V : ℝ) C.psi
      (fun n => (a n : ℂ)) (fun n => (b n : ℂ)) =
        ((pairBox C x jstar a b U V : ℝ) : ℂ) := by
  have hceilU : ⌈2 * (U : ℝ)⌉₊ = 2 * U := by
    calc
      ⌈2 * (U : ℝ)⌉₊ = ⌈((2 * U : ℕ) : ℝ)⌉₊ := by congr 1; push_cast; ring
      _ = 2 * U := Nat.ceil_natCast _
  have hceilV : ⌈2 * (V : ℝ)⌉₊ = 2 * V := by
    calc
      ⌈2 * (V : ℝ)⌉₊ = ⌈((2 * V : ℕ) : ℝ)⌉₊ := by congr 1; push_cast; ring
      _ = 2 * V := Nat.ceil_natCast _
  unfold typeIISum pairBox
  rw [Nat.ceil_natCast, Nat.ceil_natCast, hceilU, hceilV]
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  unfold pairKernel CandidateData.weighted
  split_ifs <;> push_cast <;> simp

/-- A nonzero dyadic box contains a supported pair with nonzero coefficients. -/
theorem pairBox_ne_zero {C : CandidateData} {x : ℝ} {jstar : ℕ} {a b : ℕ → ℝ}
    {U V : ℕ} (h : pairBox C x jstar a b U V ≠ 0) :
    ∃ m ∈ Finset.Ico U (2 * U), ∃ n ∈ Finset.Ico V (2 * V),
      pairKernel C x jstar m n ≠ 0 ∧ a m ≠ 0 ∧ b n ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply h
  unfold pairBox
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hk : pairKernel C x jstar m n = 0
  · simp [hk]
  · by_cases ha : a m = 0
    · simp [ha]
    · simp [hnone m hm n hn hk ha]

/-- Factor and product ranges of a supported balanced pair in a dyadic box. -/
theorem box_ranges (x bstar lo hi : ℝ) (m n u U V : ℕ) (hx : 1 ≤ x)
    (hlo : 2 * x ^ bstar ≤ lo) (hhi : hi ≤ x ^ (1 - bstar))
    (hm : lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi) (hn : lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi)
    (hmU : m ∈ Finset.Ico U (2 * U)) (hnV : n ∈ Finset.Ico V (2 * V))
    (hprod : m * n = 2 * u + 1) (hu : x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x) :
    x / 8 ≤ (U : ℝ) * (V : ℝ) ∧ (U : ℝ) * (V : ℝ) ≤ 8 * x ∧
      x ^ bstar ≤ (U : ℝ) ∧ (U : ℝ) ≤ x ^ (1 - bstar) ∧
      x ^ bstar ≤ (V : ℝ) ∧ (V : ℝ) ≤ x ^ (1 - bstar) := by
  have hprodR : (m : ℝ) * (n : ℝ) = 2 * (u : ℝ) + 1 := by exact_mod_cast hprod
  rcases Finset.mem_Ico.mp hmU with ⟨hUm, hmU2⟩
  rcases Finset.mem_Ico.mp hnV with ⟨hVn, hnV2⟩
  have hUm' : (U : ℝ) ≤ (m : ℝ) := by exact_mod_cast hUm
  have hVn' : (V : ℝ) ≤ (n : ℝ) := by exact_mod_cast hVn
  have hmU2' : (m : ℝ) < 2 * (U : ℝ) := by exact_mod_cast hmU2
  have hnV2' : (n : ℝ) < 2 * (V : ℝ) := by exact_mod_cast hnV2
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hpow0 : 0 ≤ x ^ bstar := Real.rpow_nonneg (by linarith) _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (m : ℝ) * (n : ℝ) ≤ (2 * (U : ℝ)) * (2 * (V : ℝ)) :=
      mul_le_mul hmU2'.le hnV2'.le hn0 (by linarith)
    nlinarith
  · have h1 : (U : ℝ) * (V : ℝ) ≤ (m : ℝ) * (n : ℝ) := mul_le_mul hUm' hVn' hV0 hm0
    nlinarith
  · linarith
  · linarith
  · linarith
  · linarith

end Erdos821.S10Prime
