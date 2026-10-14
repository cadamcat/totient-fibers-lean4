import Mathlib

open scoped BigOperators

namespace Erdos821.P9Core

theorem residue_count_full_block (a r c : ℕ) (hr : 0 < r) :
    ((Finset.Ico a (a + r)).filter fun n => n % r = c % r).card = 1 := by
  classical
  have himage : (Finset.Ico a (a + r)).image (fun n => n % r) = Finset.range r :=
    Nat.image_Ico_mod a r
  have hc : c % r < r := Nat.mod_lt c hr
  obtain ⟨n, hn, hmod⟩ := Finset.mem_image.mp (by rw [himage]; exact Finset.mem_range.mpr hc)
  have hinj : Set.InjOn (fun n => n % r) (Finset.Ico a (a + r) : Finset ℕ) :=
    Nat.mod_injOn_Ico a r
  have hfilter : (Finset.Ico a (a + r)).filter (fun m => m % r = c % r) = {n} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hres⟩
      have hmn : m % r = n % r := hres.trans hmod.symm
      have hmSet : m ∈ (Finset.Ico a (a + r) : Set ℕ) := by simpa using hm
      have hnSet : n ∈ (Finset.Ico a (a + r) : Set ℕ) := by simpa using hn
      have : m = n := hinj hmSet hnSet hmn
      exact this
    · intro hmn
      subst m
      exact ⟨hn, hmod⟩
  rw [hfilter, Finset.card_singleton]

theorem residue_count_multiple_blocks (a r c q : ℕ) (hr : 0 < r) :
    ((Finset.Ico a (a + q * r)).filter fun n => n % r = c % r).card = q := by
  classical
  induction q with
  | zero => simp
  | succ q ih =>
      let mid := a + q * r
      have hend : a + (q + 1) * r = mid + r := by
        calc
          a + (q + 1) * r = a + (Nat.succ q) * r := by congr 2 <;> omega
          _ = a + (q * r + r) := by rw [Nat.succ_mul]
          _ = mid + r := by simp [mid, Nat.add_assoc]
      have hsplit : Finset.Ico a (a + (q + 1) * r) =
          Finset.Ico a mid ∪ Finset.Ico mid (mid + r) := by
        rw [← hend]
        exact (Finset.Ico_union_Ico_eq_Ico (by dsimp [mid]; omega) (by omega)).symm
      have hdisj : Disjoint
          ((Finset.Ico a mid).filter fun n => n % r = c % r)
          ((Finset.Ico mid (mid + r)).filter fun n => n % r = c % r) := by
        refine Finset.disjoint_left.mpr ?_
        intro n hn hn'
        simp only [Finset.mem_filter, Finset.mem_Ico] at hn hn'
        omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih,
        residue_count_full_block mid r c hr]

theorem residue_interval_count_nat (a b r c : ℕ) (hab : a ≤ b) (hr : 0 < r) :
    |(((Finset.Ico a b).filter fun n => n % r = c % r).card : ℝ) -
        ((b - a : ℕ) : ℝ) / (r : ℝ)| ≤ 2 := by
  classical
  let length := b - a
  let q := length / r
  let s := length % r
  let mid := a + q * r
  have hdecomp : q * r + s = length := by
    dsimp [q, s, length]
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div (b - a) r
  have hslt : s < r := by dsimp [s, length]; exact Nat.mod_lt _ hr
  have hmidle : mid ≤ b := by
    dsimp [mid, q, length]
    calc
      a + (b - a) / r * r ≤ a + (b - a) := Nat.add_le_add_left (Nat.div_mul_le_self _ _) _
      _ = b := Nat.add_sub_of_le hab
  have hend : b = mid + s := by
    have hLen : b - a = q * r + s := by simpa [length] using hdecomp.symm
    calc
      b = a + (b - a) := (Nat.add_sub_of_le hab).symm
      _ = a + (q * r + s) := by rw [hLen]
      _ = mid + s := by simp [mid, Nat.add_assoc]
  have hsplit : Finset.Ico a b = Finset.Ico a mid ∪ Finset.Ico mid b := by
    have hamid : a ≤ mid := by dsimp [mid]; omega
    exact (Finset.Ico_union_Ico_eq_Ico hamid hmidle).symm
  have hdisj : Disjoint
      ((Finset.Ico a mid).filter fun n => n % r = c % r)
      ((Finset.Ico mid b).filter fun n => n % r = c % r) := by
    refine Finset.disjoint_left.mpr ?_
    intro n hn hn'
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn hn'
    omega
  have htail_le : ((Finset.Ico mid b).filter fun n => n % r = c % r).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro n m hn hm
    have hn' : n ∈ Finset.Ico mid b ∧ n % r = c % r := by simpa [Finset.mem_filter] using hn
    have hm' : m ∈ Finset.Ico mid b ∧ m % r = c % r := by simpa [Finset.mem_filter] using hm
    have hnIco : mid ≤ n ∧ n < b := Finset.mem_Ico.mp hn'.1
    have hmIco : mid ≤ m ∧ m < b := Finset.mem_Ico.mp hm'.1
    rw [hend] at hnIco hmIco
    have hblockN : n ∈ Finset.Ico mid (mid + r) := by
      exact Finset.mem_Ico.mpr ⟨hnIco.1,
        lt_of_lt_of_le hnIco.2 (Nat.add_le_add_left hslt.le mid)⟩
    have hblockM : m ∈ Finset.Ico mid (mid + r) := by
      exact Finset.mem_Ico.mpr ⟨hmIco.1,
        lt_of_lt_of_le hmIco.2 (Nat.add_le_add_left hslt.le mid)⟩
    have hblockNSet : n ∈ (Finset.Ico mid (mid + r) : Set ℕ) := by simpa using hblockN
    have hblockMSet : m ∈ (Finset.Ico mid (mid + r) : Set ℕ) := by simpa using hblockM
    exact Nat.mod_injOn_Ico mid r hblockNSet hblockMSet (hn'.2.trans hm'.2.symm)
  have hcount :
      ((Finset.Ico a b).filter fun n => n % r = c % r).card =
        q + ((Finset.Ico mid b).filter fun n => n % r = c % r).card := by
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
    rw [residue_count_multiple_blocks a r c q hr]
  have hcountLo : (q : ℝ) ≤
      (((Finset.Ico a b).filter fun n => n % r = c % r).card : ℝ) := by
    rw [hcount]
    rw [Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hcountHi :
      (((Finset.Ico a b).filter fun n => n % r = c % r).card : ℝ) ≤ q + 1 := by
    rw [hcount]
    have hcard : (↑((Finset.Ico mid b).filter fun n => n % r = c % r).card : ℝ) ≤ 1 := by
      exact_mod_cast htail_le
    rw [Nat.cast_add]
    nlinarith [hcard]
  have hdiv : ((b - a : ℕ) : ℝ) / (r : ℝ) = q + (s : ℝ) / r := by
    have hcast : ((b - a : ℕ) : ℝ) = (q : ℝ) * r + s := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) hdecomp
      simpa [length, Nat.cast_add, Nat.cast_mul] using hh.symm
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    rw [hcast]
    field_simp [hrR]
  have hsR : 0 ≤ (s : ℝ) / r := by positivity
  have hsRlt : (s : ℝ) / r < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < r)]
    exact_mod_cast hslt
  rw [abs_le]
  constructor <;> linarith [hcountLo, hcountHi, hdiv, hsR, hsRlt]

theorem pair_lattice_count_nat (a b c d r u v : ℕ) (hab : a ≤ b) (hcd : c ≤ d)
    (hr : 0 < r) :
    |(((Finset.Ico a b).filter fun n => n % r = u % r).card : ℝ) *
        (((Finset.Ico c d).filter fun n => n % r = v % r).card : ℝ) -
        ((b - a : ℕ) : ℝ) * (d - c : ℕ) / (r : ℝ) ^ 2| ≤
      4 + 2 * (((b - a : ℕ) : ℝ) + (d - c : ℕ)) / (r : ℝ) := by
  let A : ℝ := ((Finset.Ico a b).filter fun n => n % r = u % r).card
  let B : ℝ := ((Finset.Ico c d).filter fun n => n % r = v % r).card
  let X : ℝ := (b - a : ℕ) / r
  let Y : ℝ := (d - c : ℕ) / r
  have hA : |A - X| ≤ 2 := by
    simpa [A, X] using residue_interval_count_nat a b r u hab hr
  have hB : |B - Y| ≤ 2 := by
    simpa [B, Y] using residue_interval_count_nat c d r v hcd hr
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hXY : X * Y = ((b - a : ℕ) : ℝ) * (d - c : ℕ) / (r : ℝ) ^ 2 := by
    dsimp [X, Y]
    field_simp [hrR]
  have herror :
      |A * B - X * Y| ≤ |A - X| * Y + |B - Y| * X + |A - X| * |B - Y| := by
    calc
      |A * B - X * Y| = |(A - X) * Y + (B - Y) * X + (A - X) * (B - Y)| := by
        congr 1
        ring
      _ ≤ |(A - X) * Y| + |(B - Y) * X| + |(A - X) * (B - Y)| := by
        calc
          |(A - X) * Y + (B - Y) * X + (A - X) * (B - Y)| ≤
              |(A - X) * Y + (B - Y) * X| + |(A - X) * (B - Y)| := abs_add_le _ _
          _ ≤ |(A - X) * Y| + |(B - Y) * X| + |(A - X) * (B - Y)| := by
            have htri := abs_add_le ((A - X) * Y) ((B - Y) * X)
            nlinarith [htri]
      _ ≤ |A - X| * Y + |B - Y| * X + |A - X| * |B - Y| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hY, abs_of_nonneg hX]
  have hAY : |A - X| * Y ≤ 2 * Y := mul_le_mul_of_nonneg_right hA hY
  have hBX : |B - Y| * X ≤ 2 * X := mul_le_mul_of_nonneg_right hB hX
  have hAB : |A - X| * |B - Y| ≤ 4 := by
    calc
      |A - X| * |B - Y| ≤ 2 * 2 :=
        mul_le_mul hA hB (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      _ = 4 := by norm_num
  have hbound : |A * B - X * Y| ≤ 2 * Y + 2 * X + 4 := by
    calc
      |A * B - X * Y| ≤ |A - X| * Y + |B - Y| * X + |A - X| * |B - Y| := herror
      _ ≤ 2 * Y + 2 * X + 4 := by nlinarith [hAY, hBX, hAB]
  have hscale : 2 * Y + 2 * X =
      2 * (((b - a : ℕ) : ℝ) + (d - c : ℕ)) / (r : ℝ) := by
    dsimp [X, Y]
    field_simp [hrR]
    ring
  simpa [A, B, hXY, hscale, add_comm] using hbound


end Erdos821.P9Core
