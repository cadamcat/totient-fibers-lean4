import Erdos821.Blueprint.Analytic
import Erdos821.S56.Determinant
import Erdos821.S56.DeterminantConverse
import Erdos821.S56.DeterminantExistence
import Erdos821.S56.BlueprintDeterminant

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Reidx
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Copy of `Erdos821.S56Core.dyad` (`Separated.lean`), verbatim body. -/
def dyad (U : ℝ) : Finset ℕ := Finset.Ico ⌈U⌉₊ ⌈2 * U⌉₊

/-- Copy of `Erdos821.S56Core.offDiagonalSum` (`Separated.lean`), verbatim body. -/
def offDiagonalSum (E U V : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) : ℂ :=
  ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
    (etae (e / E) * etan (n / V) : ℝ) *
      ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e)))
        else 0

/-- Copy of `Erdos821.P6Off.determinantSum` (`ReindexTask.lean`), verbatim body. -/
def determinantSum (M N : ℕ) (E U V : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(M : ℤ)) M, ∑ z ∈ Finset.Icc 1 N,
    ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        (etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) *
          (alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m))
      else 0

/-- Copy of `Erdos821.P6Off.OffDiagonalReindexTask` (`ReindexTask.lean`),
verbatim body (with our copies of the sums). -/
def OffDiagonalReindexTask : Prop :=
  ∀ (M : ℕ) (E U V emin y : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ),
    0 < E → 1 ≤ U → 1 ≤ V → 0 < emin → U ≤ 2 * emin * M →
    (2 * M : ℝ) ≤ y → (∀ n, alpha n ≠ 0 → rough y n) →
    Function.support etae ⊆ Set.Icc (emin / E) 2 →
    Function.support etan ⊆ Set.Icc (1 / 2) 4 →
    offDiagonalSum E U V etae etan ah alpha =
      determinantSum M (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊) E U V etae etan ah alpha

section Helpers

theorem mem_dyad_iff (U : ℝ) (m : ℕ) :
    m ∈ dyad U ↔ ⌈U⌉₊ ≤ m ∧ m < ⌈2 * U⌉₊ := Finset.mem_Ico

theorem dyad_lower_of_mem (U : ℝ) (m : ℕ) (hm : m ∈ dyad U) : U ≤ (m : ℝ) := by
  have h1 : ⌈U⌉₊ ≤ m := ((mem_dyad_iff U m).mp hm).1
  have h2 : U ≤ ((⌈U⌉₊ : ℕ) : ℝ) := Nat.le_ceil U
  exact h2.trans (by exact_mod_cast h1)

theorem dyad_upper_of_mem (U : ℝ) (m : ℕ) (hm : m ∈ dyad U) : (m : ℝ) < 2 * U := by
  have h2 : m < ⌈2 * U⌉₊ := ((mem_dyad_iff U m).mp hm).2
  by_contra hc
  push_neg at hc
  have hle : ⌈2 * U⌉₊ ≤ m := Nat.ceil_le.mpr hc
  omega

theorem dyad_le_ceil_of_mem (U : ℝ) (m : ℕ) (hm : m ∈ dyad U) : m ≤ ⌈2 * U⌉₊ :=
  le_of_lt ((mem_dyad_iff U m).mp hm).2

theorem dyad_pos_of_mem (U : ℝ) (m : ℕ) (hU : 1 ≤ U) (hm : m ∈ dyad U) : 0 < m := by
  have hle : U ≤ (m : ℝ) := dyad_lower_of_mem U m hm
  have : (1 : ℝ) ≤ (m : ℝ) := hU.trans hle
  exact_mod_cast this

theorem dyad_diff_lt (U : ℝ) (m m' : ℕ) (hm : m ∈ dyad U) (hm' : m' ∈ dyad U) :
    |(m' : ℝ) - m| < U := by
  have h1 : U ≤ (m : ℝ) := dyad_lower_of_mem U m hm
  have h2 : U ≤ (m' : ℝ) := dyad_lower_of_mem U m' hm'
  have h3 : (m : ℝ) < 2 * U := dyad_upper_of_mem U m hm
  have h4 : (m' : ℝ) < 2 * U := dyad_upper_of_mem U m' hm'
  rw [abs_lt]
  constructor <;> linarith

theorem mem_Eset_imp_le (E : ℝ) (hE : 0 < E) (e : ℕ)
    (he : e ∈ Finset.Icc 1 ⌊2 * E⌋₊) : (e : ℝ) ≤ 2 * E := by
  have h2 : e ≤ ⌊2 * E⌋₊ := (Finset.mem_Icc.mp he).2
  have h3 : ((e : ℕ) : ℝ) ≤ ((⌊2 * E⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
  have h4 : ((⌊2 * E⌋₊ : ℕ) : ℝ) ≤ 2 * E := Nat.floor_le (by positivity)
  exact h3.trans h4

theorem mem_Nset_imp_le (V : ℝ) (hV : 0 < V) (n : ℕ)
    (hn : n ∈ Finset.Icc 1 ⌊4 * V⌋₊) : (n : ℝ) ≤ 4 * V := by
  have h2 : n ≤ ⌊4 * V⌋₊ := (Finset.mem_Icc.mp hn).2
  have h3 : ((n : ℕ) : ℝ) ≤ ((⌊4 * V⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
  have h4 : ((⌊4 * V⌋₊ : ℕ) : ℝ) ≤ 4 * V := Nat.floor_le (by positivity)
  exact h3.trans h4

theorem mem_Eset_imp_ge (E : ℝ) (e : ℕ) (he : e ∈ Finset.Icc 1 ⌊2 * E⌋₊) : 1 ≤ e :=
  (Finset.mem_Icc.mp he).1

theorem mem_Nset_imp_ge (V : ℝ) (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊4 * V⌋₊) : 1 ≤ n :=
  (Finset.mem_Icc.mp hn).1

theorem le_floor_of_le (V : ℝ) (n : ℕ) (h : (n : ℝ) ≤ 4 * V) : n ≤ ⌊4 * V⌋₊ :=
  Nat.le_floor h

theorem etae_eq_zero_of_not_mem_support (emin E : ℝ) (etae : ℝ → ℝ) (x : ℝ)
    (hsup : Function.support etae ⊆ Set.Icc (emin / E) 2)
    (hx : x ∉ Set.Icc (emin / E) 2) : etae x = 0 := by
  by_contra hne
  exact hx (hsup (Function.mem_support.mpr hne))

theorem etan_eq_zero_of_not_mem_support (etan : ℝ → ℝ) (x : ℝ)
    (hsup : Function.support etan ⊆ Set.Icc (1 / 2) 4)
    (hx : x ∉ Set.Icc (1 / 2 : ℝ) 4) : etan x = 0 := by
  by_contra hne
  exact hx (hsup (Function.mem_support.mpr hne))

/-- Turn the exact natural quotient used in offDiagonalSum back into its
factor equation. Copy of `P6Off.quotient_factor_equation`. -/
theorem quotient_factor_equation (e m n : ℕ) (hlarge : 1 < m * n)
    (hdiv : 2 * e ∣ m * n - 1) :
    m * n = 2 * e * ((m * n - 1) / (2 * e)) + 1 := by
  rw [Nat.mul_div_cancel' hdiv]
  omega

/-- Copy of `P6Off.quotient_factor_pos`. -/
theorem quotient_factor_pos (e m n : ℕ) (he : 0 < e) (hlarge : 1 < m * n)
    (hdiv : 2 * e ∣ m * n - 1) : 0 < (m * n - 1) / (2 * e) := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (by omega) hdiv
  · omega

/-- Copy of `P6Off.offDiagonal_determinant`. -/
theorem offDiagonal_determinant (e n m m' : ℕ) (he : 0 < e)
    (hne : m ≠ m') (hm : 1 < m * n) (hm' : 1 < m' * n)
    (hd : 2 * e ∣ m * n - 1) (hd' : 2 * e ∣ m' * n - 1) :
    ∃ k : ℤ, k ≠ 0 ∧ (m' : ℤ) - m = 2 * e * k ∧
      (((m' * n - 1) / (2 * e) : ℕ) : ℤ) -
        ((m * n - 1) / (2 * e) : ℕ) = k * n ∧
      (m : ℤ) * ((m' * n - 1) / (2 * e) : ℕ) -
        (m' : ℤ) * ((m * n - 1) / (2 * e) : ℕ) = k := by
  apply Erdos821.S56.determinant_shift_exists
  · exact_mod_cast he
  · exact_mod_cast quotient_factor_equation e m n hm hd
  · exact_mod_cast quotient_factor_equation e m' n hm' hd'
  · exact_mod_cast hne

/-- Copy of `P6Off.rough_coprime_natAbs`. -/
theorem rough_coprime_natAbs (y : ℝ) (m : ℕ) (k : ℤ) (hm : rough y m)
    (hk : k ≠ 0) (hsmall : (k.natAbs : ℝ) ≤ y) : Nat.Coprime m k.natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpk
  have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  have hle : (p : ℝ) ≤ k.natAbs := by exact_mod_cast Nat.le_of_dvd hkpos hpk
  exact (not_lt_of_ge (hle.trans hsmall)) (hm.2 p hp hpm)

/-- Copy of `P6Off.determinant_converse_nat`. -/
theorem determinant_converse_nat (m m' e h h' : ℕ) (k : ℤ)
    (hm : 0 < m) (he : 0 < e) (hh : 0 < h)
    (hdelta : (m' : ℤ) - m = 2 * e * k)
    (hcross : (m : ℤ) * h' - (m' : ℤ) * h = k)
    (hcop : Nat.Coprime m k.natAbs) :
    ∃! n : ℕ, 0 < n ∧ m * n = 2 * e * h + 1 ∧
      m' * n = 2 * e * h' + 1 := by
  have hcop' : IsCoprime (m : ℤ) k := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact hcop
  obtain ⟨n, hn, huniq⟩ := Erdos821.S56.determinant_converse_unique
    m m' e h h' k (by exact_mod_cast hm) (by exact_mod_cast he)
    (by exact_mod_cast hh) hdelta hcross hcop'
  refine ⟨n.toNat, ?_, ?_⟩
  · have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.1.le
    refine ⟨by omega, ?_, ?_⟩
    · exact_mod_cast (show (m : ℤ) * n.toNat = 2 * e * h + 1 by rw [hcast]; exact hn.2.1)
    · exact_mod_cast (show (m' : ℤ) * n.toNat = 2 * e * h' + 1 by rw [hcast]; exact hn.2.2)
  · intro n' hn'
    have heq : (n' : ℤ) = n := huniq n'
      ⟨by exact_mod_cast hn'.1, by exact_mod_cast hn'.2.1, by exact_mod_cast hn'.2.2⟩
    exact_mod_cast heq.trans (Int.toNat_of_nonneg hn.1.le).symm

theorem etae_ne_zero_imp_mem (emin E : ℝ) (etae : ℝ → ℝ) (x : ℝ)
    (hsup : Function.support etae ⊆ Set.Icc (emin / E) 2)
    (hx : etae x ≠ 0) : x ∈ Set.Icc (emin / E) 2 :=
  hsup (Function.mem_support.mpr hx)

theorem etan_ne_zero_imp_mem (etan : ℝ → ℝ) (x : ℝ)
    (hsup : Function.support etan ⊆ Set.Icc (1 / 2 : ℝ) 4)
    (hx : etan x ≠ 0) : x ∈ Set.Icc (1 / 2 : ℝ) 4 :=
  hsup (Function.mem_support.mpr hx)

theorem etae_ne_zero_imp_bounds (emin E : ℝ) (etae : ℝ → ℝ) (x : ℝ)
    (hsup : Function.support etae ⊆ Set.Icc (emin / E) 2)
    (hx : etae x ≠ 0) : emin / E ≤ x ∧ x ≤ 2 :=
  Set.mem_Icc.mp (etae_ne_zero_imp_mem emin E etae x hsup hx)

theorem etan_ne_zero_imp_bounds (etan : ℝ → ℝ) (x : ℝ)
    (hsup : Function.support etan ⊆ Set.Icc (1 / 2 : ℝ) 4)
    (hx : etan x ≠ 0) : 1 / 2 ≤ x ∧ x ≤ 4 :=
  Set.mem_Icc.mp (etan_ne_zero_imp_mem etan x hsup hx)

/-- From `etae (e / E) ≠ 0` deduce `emin ≤ e` as reals. -/
theorem emin_le_of_etae_ne_zero (emin E : ℝ) (hE : 0 < E) (etae : ℝ → ℝ) (e : ℕ)
    (hsup : Function.support etae ⊆ Set.Icc (emin / E) 2)
    (hx : etae ((e : ℝ) / E) ≠ 0) : emin ≤ (e : ℝ) := by
  have hb := (etae_ne_zero_imp_bounds emin E etae ((e : ℝ) / E) hsup hx).1
  exact (div_le_div_iff_of_pos_right hE).mp hb

theorem le_twoE_of_etae_ne_zero (E : ℝ) (hE : 0 < E) (emin : ℝ) (etae : ℝ → ℝ)
    (e : ℕ) (hsup : Function.support etae ⊆ Set.Icc (emin / E) 2)
    (hx : etae ((e : ℝ) / E) ≠ 0) : (e : ℝ) ≤ 2 * E := by
  have hb := (etae_ne_zero_imp_bounds emin E etae ((e : ℝ) / E) hsup hx).2
  exact (div_le_iff₀ hE).mp hb

/-- Nat.ModEq gives integer divisibility, no ordering needed. -/
theorem modEq_int_dvd (d m m' : ℕ) (h : Nat.ModEq d m m') :
    ((d : ℕ) : ℤ) ∣ ((m' : ℕ) : ℤ) - m := (Nat.modEq_iff_dvd.mp h)

/-- Forward congruence from the signed equation. -/
theorem forward_modEq (m m' e : ℕ) (k : ℤ)
    (hdelta : (m' : ℤ) - m = 2 * (e : ℤ) * k) :
    Nat.ModEq (2 * k.natAbs) m m' := by
  apply Nat.modEq_iff_dvd.mpr
  have habs : ((2 * k.natAbs : ℕ) : ℤ) = 2 * |k| := by
    push_cast
    ring
  rw [habs]
  by_cases hk0 : k = 0
  · subst hk0
    simp only [abs_zero, mul_zero]
    -- need (0:ℤ) ∣ m' - m, i.e. m' = m
    have hmm : (m' : ℤ) = (m : ℤ) := by linarith [hdelta]
    have : m' = m := by exact_mod_cast hmm
    simp [this]
  · rcases lt_trichotomy k 0 with hneg | heq | hpos
    · have hab2 : |k| = -k := abs_of_neg hneg
      rw [hab2]
      exact ⟨(-(e : ℤ)), by linarith [hdelta]⟩
    · exact absurd heq hk0
    · have hab2 : |k| = k := abs_of_pos hpos
      rw [hab2]
      exact ⟨(e : ℤ), by linarith [hdelta]⟩

/-- First cutoff matches under the signed equation. -/
theorem fwd_cutoff_eq (m m' e : ℕ) (k : ℤ) (E : ℝ)
    (hk : k ≠ 0) (hE : E ≠ 0)
    (hdelta : (m' : ℤ) - m = 2 * (e : ℤ) * k) :
    (((m' : ℝ) - m) / (2 * k * E)) = ((e : ℝ) / E) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have h2kR : (2 : ℝ) * k ≠ 0 := mul_ne_zero (by norm_num) hkR
  -- (m' - m) = 2 e k as reals
  have hdeltaR : ((m' : ℝ) - m) = 2 * (e : ℝ) * k := by exact_mod_cast hdelta
  rw [hdeltaR]
  field_simp

/-- Second cutoff matches: `(m'-m) z / (k m m' V) + 1/(m V) = n / V`
when `z = m' h`, `m'-m = 2 e k`, `m n = 2 e h + 1`. -/
theorem fwd_etan_eq (m m' e h n : ℕ) (k : ℤ) (V : ℝ) (z : ℕ)
    (hk : k ≠ 0) (hm : 0 < m) (hm' : 0 < m') (hV : V ≠ 0)
    (hdelta : (m' : ℤ) - m = 2 * (e : ℤ) * k)
    (hz : z = m' * h)
    (hmn : m * n = 2 * e * h + 1) :
    (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) = ((n : ℝ) / V) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmR' : (m' : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
  have hdeltaR : ((m' : ℝ) - m) = 2 * (e : ℝ) * k := by exact_mod_cast hdelta
  have hzR : (z : ℝ) = (m' : ℝ) * h := by rw [hz]; push_cast; ring
  have hmnR : (m : ℝ) * n = 2 * (e : ℝ) * h + 1 := by exact_mod_cast hmn
  rw [hdeltaR, hzR]
  field_simp
  -- goal: 2 e m' h + k m' = k m n m'? Let's linear combination
  have hmn2 : (k : ℝ) * (m : ℝ) * n * (m' : ℝ) =
      (k : ℝ) * (2 * (e : ℝ) * h + 1) * (m' : ℝ) := by rw [← hmnR]; ring
  linarith [hmn2]

/-- Forward `k` lies in the signed box. -/
theorem fwd_k_mem (U emin : ℝ) (M : ℕ) (m m' e : ℕ) (k : ℤ)
    (hm : m ∈ dyad U) (hm' : m' ∈ dyad U)
    (he_pos : 0 < (e : ℝ)) (he_min : emin ≤ (e : ℝ)) (hemin_pos : 0 < emin)
    (hU : U ≤ 2 * emin * M)
    (hdelta : (m' : ℤ) - m = 2 * (e : ℤ) * k) :
    k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
  have hdiff : |(m' : ℝ) - m| < U := dyad_diff_lt U m m' hm hm'
  have hdeltaR : ((m' : ℝ) - m) = 2 * (e : ℝ) * (k : ℝ) := by exact_mod_cast hdelta
  have he2pos : (0 : ℝ) < 2 * (e : ℝ) := by positivity
  have hemin2pos : (0 : ℝ) < 2 * emin := by positivity
  have hle_den : 2 * emin ≤ 2 * (e : ℝ) := by linarith [he_min]
  have habs : |(m' : ℝ) - m| = (2 * (e : ℝ)) * |(k : ℝ)| := by
    rw [hdeltaR, abs_mul, abs_of_pos he2pos]
  have hkle : |(k : ℝ)| = |(m' : ℝ) - m| / (2 * (e : ℝ)) := by
    rw [habs]
    field_simp
  have h1 : |(m' : ℝ) - m| / (2 * (e : ℝ)) ≤ |(m' : ℝ) - m| / (2 * emin) :=
    div_le_div_of_nonneg_left (abs_nonneg _) hemin2pos hle_den
  have h2 : |(m' : ℝ) - m| / (2 * emin) < U / (2 * emin) := by
    gcongr
  have hUM : U ≤ (M : ℝ) * (2 * emin) := by
    calc U ≤ 2 * emin * (M : ℝ) := hU
      _ = (M : ℝ) * (2 * emin) := by ring
  have h3 : U / (2 * emin) ≤ (M : ℝ) := (div_le_iff₀ hemin2pos).mpr hUM
  have hk_le : |(k : ℝ)| ≤ (M : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_of_eq hkle) h1)
      (lt_of_lt_of_le h2 h3))
  have habs_le := abs_le.mp hk_le
  rw [Finset.mem_Icc]
  constructor
  · have hreal : (-(M : ℝ)) ≤ (k : ℝ) := habs_le.1
    have hcast : ((-(M : ℤ) : ℤ) : ℝ) = (-(M : ℝ)) := by push_cast; ring
    have hle : ((-(M : ℤ) : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by rw [hcast]; exact hreal
    exact_mod_cast hle
  · have hreal : (k : ℝ) ≤ (M : ℝ) := habs_le.2
    have hcast : (((M : ℤ) : ℤ) : ℝ) = ((M : ℝ)) := by push_cast; ring
    have hle : ((k : ℤ) : ℝ) ≤ (((M : ℤ) : ℤ) : ℝ) := by rw [hcast]; exact hreal
    exact_mod_cast hle

/-- Forward `z = m' * h` lies in the generous box. -/
theorem fwd_z_mem (U V : ℝ) (m m' n e : ℕ) (h : ℕ)
    (hm : m ∈ dyad U) (hm' : m' ∈ dyad U)
    (hn : n ∈ Finset.Icc 1 ⌊4 * V⌋₊)
    (hh : h = (m * n - 1) / (2 * e))
    (hh_pos : 0 < h) (hm'_pos : 0 < m') :
    m' * h ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊) := by
  have hm_le : m ≤ ⌈2 * U⌉₊ := dyad_le_ceil_of_mem U m hm
  have hm'_le : m' ≤ ⌈2 * U⌉₊ := dyad_le_ceil_of_mem U m' hm'
  have hn_le : n ≤ ⌊4 * V⌋₊ := (Finset.mem_Icc.mp hn).2
  have hh_le : h ≤ m * n := by
    rw [hh]
    calc (m * n - 1) / (2 * e) ≤ m * n - 1 := Nat.div_le_self _ _
      _ ≤ m * n := Nat.sub_le _ _
  have hmn_le : m * n ≤ ⌈2 * U⌉₊ * ⌊4 * V⌋₊ := Nat.mul_le_mul hm_le hn_le
  have hh_le2 : h ≤ ⌈2 * U⌉₊ * ⌊4 * V⌋₊ := hh_le.trans hmn_le
  have hz_le : m' * h ≤ ⌈2 * U⌉₊ * (⌈2 * U⌉₊ * ⌊4 * V⌋₊) :=
    Nat.mul_le_mul hm'_le hh_le2
  have hz_eq : ⌈2 * U⌉₊ * (⌈2 * U⌉₊ * ⌊4 * V⌋₊) = ⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊ := by
    ring
  rw [Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · exact Nat.succ_le_iff.mpr (Nat.mul_pos hm'_pos hh_pos)
  · calc m' * h ≤ ⌈2 * U⌉₊ * (⌈2 * U⌉₊ * ⌊4 * V⌋₊) := hz_le
      _ = ⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊ := hz_eq

/-- Reverse `e` from the first cutoff and congruence. -/
theorem rev_e_exists (m m' : ℕ) (k : ℤ) (E emin : ℝ) (etae : ℝ → ℝ)
    (hk : k ≠ 0) (hE : 0 < E) (hemin : 0 < emin)
    (hmod : Nat.ModEq (2 * k.natAbs) m m')
    (hsup : Function.support etae ⊆ Set.Icc (emin / E) 2)
    (hcut : etae (((m' : ℝ) - m) / (2 * k * E)) ≠ 0) :
    ∃ e : ℕ, 0 < e ∧ (m' : ℤ) - m = 2 * (e : ℤ) * k ∧
      ((e : ℝ) = ((m' : ℝ) - m) / (2 * k)) ∧ emin ≤ (e : ℝ) ∧ (e : ℝ) ≤ 2 * E := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hmem := etae_ne_zero_imp_mem emin E etae _ hsup hcut
  have hb := Set.mem_Icc.mp hmem
  have hXpos : (0 : ℝ) < ((m' : ℝ) - m) / (2 * k * E) := by
    have hpos : (0 : ℝ) < emin / E := by positivity
    linarith [hb.1]
  have hXE : ((m' : ℝ) - m) / (2 * k) = (((m' : ℝ) - m) / (2 * k * E)) * E := by
    field_simp
  have hpos2 : (0 : ℝ) < ((m' : ℝ) - m) / (2 * k) := by
    rw [hXE]; exact mul_pos hXpos hE
  have hEbound1 : emin ≤ ((m' : ℝ) - m) / (2 * k) := by
    rw [hXE]
    have hem : emin = (emin / E) * E := by field_simp
    rw [hem]
    exact mul_le_mul_of_nonneg_right hb.1 (le_of_lt hE)
  have hEbound2 : ((m' : ℝ) - m) / (2 * k) ≤ 2 * E := by
    rw [hXE]
    exact mul_le_mul_of_nonneg_right hb.2 (le_of_lt hE)
  have hdvd_int : ((2 * k.natAbs : ℕ) : ℤ) ∣ ((m' : ℕ) : ℤ) - m :=
    modEq_int_dvd _ _ _ hmod
  have hkpos_nat : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  rcases lt_trichotomy (k : ℝ) 0 with hkneg | hkzero | hkpos
  · have hk_neg : k < 0 := by exact_mod_cast hkneg
    have hdiff_neg : ((m' : ℝ) - m) < 0 := by
      have hk2neg : (2 : ℝ) * (k : ℝ) < 0 := by linarith
      rcases (div_pos_iff.mp hpos2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · exact h1
    have hlt_nm : m' < m := by
      by_contra hc
      push_neg at hc
      have hleR : ((m : ℝ)) ≤ (m' : ℝ) := by exact_mod_cast hc
      linarith
    have hle : m' ≤ m := le_of_lt hlt_nm
    have hcast_sub : (((m - m' : ℕ) : ℕ) : ℤ) = (m : ℤ) - m' := by
      rw [Nat.cast_sub hle]
    have hdvd_nat : 2 * k.natAbs ∣ m - m' := by
      have h1 : ((2 * k.natAbs : ℕ) : ℤ) ∣ ((m - m' : ℕ) : ℤ) := by
        rw [hcast_sub]
        have hsym : (m : ℤ) - m' = -(((m' : ℕ) : ℤ) - m) := by ring
        rw [hsym]; exact dvd_neg.mpr hdvd_int
      exact Int.natCast_dvd_natCast.mp h1
    obtain ⟨e, he⟩ := hdvd_nat
    have he_pos : 0 < e := by
      by_contra hc
      push_neg at hc
      have he0 : e = 0 := Nat.le_zero.mp hc
      rw [he0, Nat.mul_zero] at he
      have hmm : m = m' := by omega
      have hzero : ((m' : ℝ) - (m : ℝ)) = 0 := by rw [hmm]; ring
      rw [hzero, zero_div] at hpos2
      exact lt_irrefl 0 hpos2
    have hk_abs : |k| = -k := abs_of_neg hk_neg
    have habs_nat : ((k.natAbs : ℕ) : ℤ) = |k| := Int.natCast_natAbs k
    have hk_eq : ((k.natAbs : ℕ) : ℤ) = -k := by rw [habs_nat, hk_abs]
    have hdelta_e : (m' : ℤ) - m = 2 * (e : ℤ) * k := by
      have h1 : (m : ℤ) - m' = 2 * ((k.natAbs : ℕ) : ℤ) * (e : ℤ) := by
        have hsub : ((m - m' : ℕ) : ℤ) = (m : ℤ) - m' := by rw [Nat.cast_sub hle]
        calc (m : ℤ) - m' = ((m - m' : ℕ) : ℤ) := hsub.symm
          _ = ((2 * k.natAbs * e : ℕ) : ℤ) := by rw [he]
          _ = 2 * ((k.natAbs : ℕ) : ℤ) * (e : ℤ) := by push_cast; ring
      rw [hk_eq] at h1
      linarith
    have hdeltaR : ((m' : ℝ) - (m : ℝ)) = 2 * (e : ℝ) * (k : ℝ) := by
      exact_mod_cast hdelta_e
    have heR : (e : ℝ) = ((m' : ℝ) - m) / (2 * (k : ℝ)) := by
      rw [hdeltaR]; field_simp
    exact ⟨e, he_pos, hdelta_e, heR, heR ▸ hEbound1, heR ▸ hEbound2⟩
  · exfalso; exact hkR hkzero
  · have hk_pos : 0 < k := by exact_mod_cast hkpos
    have hdiff_pos : (0 : ℝ) < ((m' : ℝ) - m) := by
      have hk2pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
      rcases (div_pos_iff.mp hpos2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · linarith [hk2pos, h2]
    have hlt_nm : m < m' := by
      by_contra hc
      push_neg at hc
      have hleR : ((m' : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hc
      linarith
    have hle : m ≤ m' := le_of_lt hlt_nm
    have hcast_sub : (((m' - m : ℕ) : ℕ) : ℤ) = (m' : ℤ) - m := by
      rw [Nat.cast_sub hle]
    have hdvd_nat : 2 * k.natAbs ∣ m' - m := by
      have h1 : ((2 * k.natAbs : ℕ) : ℤ) ∣ ((m' - m : ℕ) : ℤ) := by
        rw [hcast_sub]; exact hdvd_int
      exact Int.natCast_dvd_natCast.mp h1
    obtain ⟨e, he⟩ := hdvd_nat
    have he_pos : 0 < e := by
      by_contra hc
      push_neg at hc
      have he0 : e = 0 := Nat.le_zero.mp hc
      rw [he0, Nat.mul_zero] at he
      have hmm : m' = m := by omega
      have hzero : ((m' : ℝ) - (m : ℝ)) = 0 := by rw [hmm]; ring
      rw [hzero, zero_div] at hpos2
      exact lt_irrefl 0 hpos2
    have hk_abs : |k| = k := abs_of_pos hk_pos
    have habs_nat : ((k.natAbs : ℕ) : ℤ) = |k| := Int.natCast_natAbs k
    have hk_eq : ((k.natAbs : ℕ) : ℤ) = k := by rw [habs_nat, hk_abs]
    have hdelta_e : (m' : ℤ) - m = 2 * (e : ℤ) * k := by
      calc (m' : ℤ) - m = ((m' - m : ℕ) : ℤ) := hcast_sub.symm
        _ = ((2 * k.natAbs * e : ℕ) : ℤ) := by rw [he]
        _ = 2 * ((k.natAbs : ℕ) : ℤ) * (e : ℤ) := by push_cast; ring
        _ = 2 * (e : ℤ) * k := by rw [hk_eq]; ring
    have hdeltaR : ((m' : ℝ) - (m : ℝ)) = 2 * (e : ℝ) * (k : ℝ) := by
      exact_mod_cast hdelta_e
    have heR : (e : ℝ) = ((m' : ℝ) - m) / (2 * (k : ℝ)) := by
      rw [hdeltaR]; field_simp
    exact ⟨e, he_pos, hdelta_e, heR, heR ▸ hEbound1, heR ▸ hEbound2⟩

/-- `k.natAbs` is small when `k` is in the box and `2M ≤ y`. -/
theorem k_natAbs_le_y (M : ℕ) (y : ℝ) (k : ℤ)
    (hk : k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hy : (2 * M : ℝ) ≤ y) :
    ((k.natAbs : ℕ) : ℝ) ≤ y := by
  have h1 : -(M : ℤ) ≤ k := (Finset.mem_Icc.mp hk).1
  have h2 : k ≤ (M : ℤ) := (Finset.mem_Icc.mp hk).2
  have habs : |k| ≤ (M : ℤ) := abs_le.mpr ⟨by linarith, h2⟩
  have hnat : ((k.natAbs : ℕ) : ℤ) = |k| := Int.natCast_natAbs k
  have hle_int : ((k.natAbs : ℕ) : ℤ) ≤ (M : ℤ) := by rw [hnat]; exact habs
  have hle_real : (((k.natAbs : ℕ) : ℤ) : ℝ) ≤ (((M : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hle_int
  have hcastM : ((((M : ℤ) : ℤ)) : ℝ) = ((M : ℕ) : ℝ) := by simp
  have hcastK : ((((k.natAbs : ℕ) : ℤ)) : ℝ) = ((k.natAbs : ℕ) : ℝ) := by simp
  rw [hcastK, hcastM] at hle_real
  have hMle : ((M : ℕ) : ℝ) ≤ y := by
    have h2M : (2 : ℝ) * M ≤ y := hy
    have hMnonneg : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    linarith
  exact hle_real.trans hMle

/-- Exact nat division when the product form holds. -/
theorem div_exact_of_mul (a b c : ℕ) (hb : 0 < b) (h : a = b * c) : a / b = c := by
  rw [h]
  exact Nat.mul_div_cancel_left c hb

/-- Reverse `h,h'` from divisibility and positivity. -/
theorem rev_h_eq (m m' z : ℕ) (k : ℤ) (hm'_pos : 0 < m') (hm_pos : 0 < m)
    (hz_pos : 0 < z) (hzk_pos : 0 < ((z : ℤ) + k).toNat)
    (hdvd1 : m' ∣ z) (hdvd2 : m ∣ ((z : ℤ) + k).toNat) :
    0 < z / m' ∧ 0 < ((z : ℤ) + k).toNat / m ∧
      z = m' * (z / m') ∧ ((z : ℤ) + k).toNat = m * (((z : ℤ) + k).toNat / m) := by
  have h1 : 0 < z / m' := Nat.div_pos (Nat.le_of_dvd hz_pos hdvd1) hm'_pos
  have h2 : 0 < ((z : ℤ) + k).toNat / m := Nat.div_pos (Nat.le_of_dvd hzk_pos hdvd2) hm_pos
  obtain ⟨c1, hc1⟩ := hdvd1
  obtain ⟨c2, hc2⟩ := hdvd2
  have hz_eq : z = m' * (z / m') := by
    rw [hc1, Nat.mul_div_cancel_left _ hm'_pos]
  have hzk_eq : ((z : ℤ) + k).toNat = m * (((z : ℤ) + k).toNat / m) := by
    rw [hc2, Nat.mul_div_cancel_left _ hm_pos]
  exact ⟨h1, h2, hz_eq, hzk_eq⟩

/-- The cross equation from `z = m' h` and `(z+k).toNat = m h'`. -/
theorem rev_hcross (m m' h h' : ℕ) (z : ℕ) (k : ℤ)
    (hz : z = m' * h)
    (hzk_nat : ((z : ℤ) + k).toNat = m * h')
    (hzk_pos : 0 < (z : ℤ) + k) :
    (m : ℤ) * h' - (m' : ℤ) * h = k := by
  have htoNat : ((((z : ℤ) + k).toNat : ℕ) : ℤ) = (z : ℤ) + k :=
    Int.toNat_of_nonneg (le_of_lt hzk_pos)
  have hzR : (z : ℤ) = (m' : ℤ) * h := by rw [hz]; push_cast; ring
  have hzkR : ((((z : ℤ) + k).toNat : ℕ) : ℤ) = (m : ℤ) * h' := by
    rw [hzk_nat]; push_cast; ring
  linarith [htoNat, hzR, hzkR]

end Helpers

section Main

/-- Inner distribution for the off-diagonal sum. -/
theorem offDiagonal_inner_eq (E U V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ)
    (e n : ℕ) :
    ((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ) *
        (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
          if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
              2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
            alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e)))
          else 0) =
      ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m' _
  by_cases h : m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
      2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1
  · simp [h]
  · simp [h]

/-- When `m = m'`, the LHS inner double sum over `e,n` vanishes per pair,
and the RHS sum vanishes via `etae 0 = 0`. -/
theorem per_pair_diag_lhs (E V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ)
    (m : ℕ) (e : ℕ) (n : ℕ) :
    (if m ≠ m ∧ 1 < m * n ∧ 1 < m * n ∧
        2 * e ∣ m * n - 1 ∧ 2 * e ∣ m * n - 1 then
      (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
        (alpha m * ah ((m * n - 1) / (2 * e)) *
          star (alpha m * ah ((m * n - 1) / (2 * e))))
    else 0) = 0 := by
  simp

theorem etae_zero_of_diag (emin E : ℝ) (hE : 0 < E) (hemin : 0 < emin)
    (etae : ℝ → ℝ) (hsup : Function.support etae ⊆ Set.Icc (emin / E) 2) :
    etae 0 = 0 := by
  apply etae_eq_zero_of_not_mem_support emin E etae 0 hsup
  simp only [Set.mem_Icc, not_and]
  intro _
  have hpos : (0 : ℝ) < emin / E := by positivity
  linarith

/-- Per-pair equality for distinct `m,m'` with nonzero `alpha`.
The filtered bijection is proved below; zeros outside are direct. -/
theorem per_pair_eq_of_ne_of_alpha (M : ℕ) (E U V emin y : ℝ)
    (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ) (m m' : ℕ)
    (hE : 0 < E) (hU : 1 ≤ U) (hV : 1 ≤ V) (hemin : 0 < emin)
    (hUM : U ≤ 2 * emin * M) (hy : (2 * M : ℝ) ≤ y)
    (hrough : ∀ n, alpha n ≠ 0 → rough y n)
    (hsupE : Function.support etae ⊆ Set.Icc (emin / E) 2)
    (hsupN : Function.support etan ⊆ Set.Icc (1 / 2 : ℝ) 4)
    (hm : m ∈ dyad U) (hm' : m' ∈ dyad U)
    (hne : m ≠ m') (ham : alpha m ≠ 0) (ham' : alpha m' ≠ 0) :
    (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
        (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e))))
      else 0) =
    (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
      else 0) := by
  -- Abbreviations for the index sets
  set Eset := Finset.Icc 1 ⌊2 * E⌋₊ with hEset
  set Nset := Finset.Icc 1 ⌊4 * V⌋₊ with hNset
  set Kset := Finset.Icc (-(M : ℤ)) (M : ℤ) with hKset
  set Zset := Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊) with hZset
  -- Predicates and cutoffs
  have hm_pos : 0 < m := dyad_pos_of_mem U m hU hm
  have hm'_pos : 0 < m' := dyad_pos_of_mem U m' hU hm'
  have hVpos : 0 < V := by linarith
  -- Full product sums
  have hLprod : (∑ e ∈ Eset, ∑ n ∈ Nset,
        (if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0)) =
      ∑ p ∈ Eset ×ˢ Nset,
        (if m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
            2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1 then
          (((etae ((p.1 : ℝ) / E) * etan ((p.2 : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * p.2 - 1) / (2 * p.1)) *
              star (alpha m' * ah ((m' * p.2 - 1) / (2 * p.1))))
        else 0) := by
    rw [Finset.sum_product]
  have hRprod : (∑ k ∈ Kset, ∑ z ∈ Zset,
        (if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0)) =
      ∑ q ∈ Kset ×ˢ Zset,
        (if q.1 ≠ 0 ∧ 0 < (q.2 : ℤ) + q.1 ∧ m' ∣ q.2 ∧ m ∣ ((q.2 : ℤ) + q.1).toNat ∧
            Nat.ModEq (2 * q.1.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * q.1 * E)) *
            etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (q.2 / m')) * star (alpha m' * ah (((q.2 : ℤ) + q.1).toNat / m)))
        else 0) := by
    rw [Finset.sum_product]
  rw [hLprod, hRprod]
  -- Filtered good sets
  set GoodL := (Eset ×ˢ Nset).filter (fun p : ℕ × ℕ =>
    (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
      2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧
    etae ((p.1 : ℝ) / E) ≠ 0 ∧ etan ((p.2 : ℝ) / V) ≠ 0) with hGoodL
  set GoodR := (Kset ×ˢ Zset).filter (fun q : ℤ × ℕ =>
    (q.1 ≠ 0 ∧ 0 < (q.2 : ℤ) + q.1 ∧ m' ∣ q.2 ∧ m ∣ ((q.2 : ℤ) + q.1).toNat ∧
      Nat.ModEq (2 * q.1.natAbs) m m') ∧
    etae (((m' : ℝ) - m) / (2 * q.1 * E)) ≠ 0 ∧
    etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) ≠ 0) with hGoodR
  have hLsub : GoodL ⊆ Eset ×ˢ Nset := Finset.filter_subset _ _
  have hRsub : GoodR ⊆ Kset ×ˢ Zset := Finset.filter_subset _ _
  have hLzero : ∀ p ∈ Eset ×ˢ Nset, p ∉ GoodL →
      (if m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
          2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1 then
        (((etae ((p.1 : ℝ) / E) * etan ((p.2 : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * p.2 - 1) / (2 * p.1)) *
            star (alpha m' * ah ((m' * p.2 - 1) / (2 * p.1))))
      else 0) = 0 := by
    intro p hp hpnot
    have hcond_false : ¬(((m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧
      etae ((p.1 : ℝ) / E) ≠ 0 ∧ etan ((p.2 : ℝ) / V) ≠ 0)) := by
      intro hcond
      exact hpnot (Finset.mem_filter.mpr ⟨hp, hcond⟩)
    by_cases hP : m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1
    · have hnot : ¬(etae ((p.1 : ℝ) / E) ≠ 0 ∧ etan ((p.2 : ℝ) / V) ≠ 0) :=
        fun h => hcond_false ⟨hP, h⟩
      have hC0 : ((etae ((p.1 : ℝ) / E) * etan ((p.2 : ℝ) / V) : ℝ) : ℂ) = 0 := by
        by_cases hE0 : etae ((p.1 : ℝ) / E) = 0
        · simp [hE0]
        · have hN0 : etan ((p.2 : ℝ) / V) = 0 := by
            by_contra hNne
            exact hnot ⟨hE0, hNne⟩
          simp [hN0]
      simp [hP, hC0]
    · simp [hP]
  have hRzero : ∀ q ∈ Kset ×ˢ Zset, q ∉ GoodR →
      (if q.1 ≠ 0 ∧ 0 < (q.2 : ℤ) + q.1 ∧ m' ∣ q.2 ∧ m ∣ ((q.2 : ℤ) + q.1).toNat ∧
          Nat.ModEq (2 * q.1.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * q.1 * E)) *
          etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (q.2 / m')) * star (alpha m' * ah (((q.2 : ℤ) + q.1).toNat / m)))
      else 0) = 0 := by
    intro q hq hqnot
    have hcond_false : ¬((((q.1 ≠ 0 ∧ 0 < (q.2 : ℤ) + q.1 ∧ m' ∣ q.2 ∧
        m ∣ ((q.2 : ℤ) + q.1).toNat ∧ Nat.ModEq (2 * q.1.natAbs) m m') ∧
      etae (((m' : ℝ) - m) / (2 * q.1 * E)) ≠ 0 ∧
      etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) ≠ 0))) := by
      intro hcond
      exact hqnot (Finset.mem_filter.mpr ⟨hq, hcond⟩)
    by_cases hQ : q.1 ≠ 0 ∧ 0 < (q.2 : ℤ) + q.1 ∧ m' ∣ q.2 ∧
        m ∣ ((q.2 : ℤ) + q.1).toNat ∧ Nat.ModEq (2 * q.1.natAbs) m m'
    · have hnot : ¬(etae (((m' : ℝ) - m) / (2 * q.1 * E)) ≠ 0 ∧
          etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) ≠ 0) :=
        fun h => hcond_false ⟨hQ, h⟩
      have hD0 : ((etae (((m' : ℝ) - m) / (2 * q.1 * E)) *
          etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) = 0 := by
        by_cases hE0 : etae (((m' : ℝ) - m) / (2 * q.1 * E)) = 0
        · rw [hE0, zero_mul, Complex.ofReal_zero]
        · have hN0 : etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) = 0 := by
            by_contra hNne
            exact hnot ⟨hE0, hNne⟩
          rw [hN0, mul_zero, Complex.ofReal_zero]
      rw [if_pos hQ, hD0, zero_mul]
    · rw [if_neg hQ]
  -- Reduce to good sets
  have hLred : (∑ p ∈ Eset ×ˢ Nset,
        (if m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
            2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1 then
          (((etae ((p.1 : ℝ) / E) * etan ((p.2 : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * p.2 - 1) / (2 * p.1)) *
              star (alpha m' * ah ((m' * p.2 - 1) / (2 * p.1))))
        else 0)) =
      ∑ p ∈ GoodL,
        (if m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
            2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1 then
          (((etae ((p.1 : ℝ) / E) * etan ((p.2 : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * p.2 - 1) / (2 * p.1)) *
              star (alpha m' * ah ((m' * p.2 - 1) / (2 * p.1))))
        else 0) :=
    (Finset.sum_subset hLsub hLzero).symm
  have hRred : (∑ q ∈ Kset ×ˢ Zset,
        (if q.1 ≠ 0 ∧ 0 < (q.2 : ℤ) + q.1 ∧ m' ∣ q.2 ∧ m ∣ ((q.2 : ℤ) + q.1).toNat ∧
            Nat.ModEq (2 * q.1.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * q.1 * E)) *
            etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (q.2 / m')) * star (alpha m' * ah (((q.2 : ℤ) + q.1).toNat / m)))
        else 0)) =
      ∑ q ∈ GoodR,
        (if q.1 ≠ 0 ∧ 0 < (q.2 : ℤ) + q.1 ∧ m' ∣ q.2 ∧ m ∣ ((q.2 : ℤ) + q.1).toNat ∧
            Nat.ModEq (2 * q.1.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * q.1 * E)) *
            etan (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (q.2 / m')) * star (alpha m' * ah (((q.2 : ℤ) + q.1).toNat / m)))
        else 0) :=
    (Finset.sum_subset hRsub hRzero).symm
  rw [hLred, hRred]
  -- Bijection between good sets (forward map via determinant, no ha in map)
  refine Finset.sum_nbij (fun p : ℕ × ℕ =>
    if h : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 then
      (Classical.choose
        (offDiagonal_determinant p.1 p.2 m m' h.2 h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2),
        m' * ((m * p.2 - 1) / (2 * p.1)))
    else (0, 1)) ?_ ?_ ?_ ?_
  · -- hi: forward lands in GoodR
    intro p hp
    have hmemF := Finset.mem_filter.mp (hGoodL ▸ hp)
    obtain ⟨hp_mem, hcond⟩ := hmemF
    obtain ⟨hP, hCE, hCN⟩ := hcond
    obtain ⟨hne', h1, h2, hd, hd'⟩ := hP
    have hmemE : p.1 ∈ Eset := (Finset.mem_product.mp hp_mem).1
    have hmemN : p.2 ∈ Nset := (Finset.mem_product.mp hp_mem).2
    have he_pos : 0 < p.1 := by
      have : 1 ≤ p.1 := mem_Eset_imp_ge E p.1 (hEset ▸ hmemE)
      omega
    have hcondP : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 :=
      ⟨⟨hne', h1, h2, hd, hd'⟩, he_pos⟩
    have hexists := offDiagonal_determinant p.1 p.2 m m' he_pos hne' h1 h2 hd hd'
    have hspec := Classical.choose_spec hexists
    obtain ⟨hk_ne, hdelta, hincr, hcross⟩ := hspec
    have hmn : m * p.2 = 2 * p.1 * ((m * p.2 - 1) / (2 * p.1)) + 1 :=
      quotient_factor_equation p.1 m p.2 h1 hd
    have hmn' : m' * p.2 = 2 * p.1 * ((m' * p.2 - 1) / (2 * p.1)) + 1 :=
      quotient_factor_equation p.1 m' p.2 h2 hd'
    have hh_pos : 0 < (m * p.2 - 1) / (2 * p.1) :=
      quotient_factor_pos p.1 m p.2 he_pos h1 hd
    have he_min : emin ≤ (p.1 : ℝ) :=
      emin_le_of_etae_ne_zero emin E hE etae p.1 hsupE hCE
    have he_posR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast he_pos
    have hk_mem : Classical.choose hexists ∈ Kset := by
      have hmemIcc := fwd_k_mem U emin M m m' p.1 (Classical.choose hexists)
        hm hm' he_posR he_min hemin hUM hdelta
      rw [hKset]
      exact hmemIcc
    have hmemN_Icc : p.2 ∈ Finset.Icc 1 ⌊4 * V⌋₊ := hNset ▸ hmemN
    have hz_mem : m' * ((m * p.2 - 1) / (2 * p.1)) ∈ Zset := by
      have hmemIcc := fwd_z_mem U V m m' p.2 p.1 ((m * p.2 - 1) / (2 * p.1))
        hm hm' hmemN_Icc rfl
        (quotient_factor_pos p.1 m p.2 he_pos h1 hd) hm'_pos
      rw [hZset]
      exact hmemIcc
    -- Q holds (with sorries for subparts to fill next)
    have hQ : Classical.choose hexists ≠ 0 ∧
        0 < ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) + Classical.choose hexists ∧
        m' ∣ m' * ((m * p.2 - 1) / (2 * p.1)) ∧
        m ∣ (((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists).toNat ∧
        Nat.ModEq (2 * (Classical.choose hexists).natAbs) m m' := by
      have hh'_pos : 0 < (m' * p.2 - 1) / (2 * p.1) :=
        quotient_factor_pos p.1 m' p.2 he_pos h2 hd'
      have hmn' : m' * p.2 = 2 * p.1 * ((m' * p.2 - 1) / (2 * p.1)) + 1 :=
        quotient_factor_equation p.1 m' p.2 h2 hd'
      -- z + k = m * h' as integers
      have hz_eq_int : ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists = (m : ℤ) * (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by
        have h1 : ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) =
            (m' : ℤ) * (((m * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by push_cast; ring
        rw [h1]
        linarith [hcross]
      have hpos_mh' : (0 : ℤ) < (m : ℤ) * (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by
        have hm_pos_int : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm_pos
        have hh'_pos_int : (0 : ℤ) < (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by
          exact_mod_cast hh'_pos
        exact mul_pos hm_pos_int hh'_pos_int
      refine ⟨hk_ne, ?_, dvd_mul_right m' _, ?_, forward_modEq m m' p.1 _ hdelta⟩
      · rw [hz_eq_int]; exact hpos_mh'
      · -- m ∣ (z+k).toNat via (z+k).toNat = m * h'
        have hzk_pos : (0 : ℤ) < ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
            Classical.choose hexists := by rw [hz_eq_int]; exact hpos_mh'
        have htoNat_eq : (((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
            Classical.choose hexists).toNat = m * ((m' * p.2 - 1) / (2 * p.1)) := by
          have hcast_mh' : (((m * ((m' * p.2 - 1) / (2 * p.1)) : ℕ)) : ℤ) =
              (m : ℤ) * (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by push_cast; ring
          have hzk_nonneg : (0 : ℤ) ≤ ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists := le_of_lt hzk_pos
          have htoNat : (((((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists).toNat : ℕ) : ℤ) =
              ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists :=
            Int.toNat_of_nonneg hzk_nonneg
          have hcast_eq : (((((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists).toNat : ℕ) : ℤ) =
              (((m * ((m' * p.2 - 1) / (2 * p.1)) : ℕ)) : ℤ) := by
            rw [htoNat, hz_eq_int, ← hcast_mh']
          exact Int.ofNat_inj.mp hcast_eq
        rw [htoNat_eq]
        exact dvd_mul_right m _
    have hDE : etae (((m' : ℝ) - m) / (2 * Classical.choose hexists * E)) ≠ 0 := by
      have hEne : E ≠ 0 := ne_of_gt hE
      have heq := fwd_cutoff_eq m m' p.1 (Classical.choose hexists) E hk_ne hEne hdelta
      -- heq : ((m'-m)/(2*k*E)) = (e/E) with e=p.1
      rw [heq]
      exact hCE
    have hDN : etan (((m' : ℝ) - m) * ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℝ) /
        (Classical.choose hexists * m * m' * V) + 1 / (m * V)) ≠ 0 := by
      have hVne : V ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < V)
      have heq := fwd_etan_eq m m' p.1 ((m * p.2 - 1) / (2 * p.1)) p.2
        (Classical.choose hexists) V (m' * ((m * p.2 - 1) / (2 * p.1)))
        hk_ne hm_pos hm'_pos hVne hdelta rfl hmn
      -- heq : S = (n/V) with n=p.2, z=m'*h
      rw [heq]
      exact hCN
    have hmemProd : (Classical.choose hexists,
        m' * ((m * p.2 - 1) / (2 * p.1))) ∈ Kset ×ˢ Zset :=
      Finset.mem_product.mpr ⟨hk_mem, hz_mem⟩
    have hcondR : ((Classical.choose hexists ≠ 0 ∧
        0 < ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) + Classical.choose hexists ∧
        m' ∣ m' * ((m * p.2 - 1) / (2 * p.1)) ∧
        m ∣ (((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists).toNat ∧
        Nat.ModEq (2 * (Classical.choose hexists).natAbs) m m') ∧
      etae (((m' : ℝ) - m) / (2 * Classical.choose hexists * E)) ≠ 0 ∧
      etan (((m' : ℝ) - m) * ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℝ) /
        (Classical.choose hexists * m * m' * V) + 1 / (m * V)) ≠ 0) :=
      ⟨hQ, hDE, hDN⟩
    have hmemR : (Classical.choose hexists, m' * ((m * p.2 - 1) / (2 * p.1))) ∈ GoodR := by
      rw [hGoodR]
      refine Finset.mem_filter.mpr ⟨hmemProd, ?_⟩
      show ((Classical.choose hexists ≠ 0 ∧
        0 < ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) + Classical.choose hexists ∧
        m' ∣ m' * ((m * p.2 - 1) / (2 * p.1)) ∧
        m ∣ (((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists).toNat ∧
        Nat.ModEq (2 * (Classical.choose hexists).natAbs) m m') ∧
      etae (((m' : ℝ) - m) / (2 * Classical.choose hexists * E)) ≠ 0 ∧
      etan (((m' : ℝ) - m) * ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℝ) /
        (Classical.choose hexists * m * m' * V) + 1 / (m * V)) ≠ 0)
      exact hcondR
    -- rewrite i p via dif_pos to match hmemR
    have hi_eq : (if h : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 then
      (Classical.choose
        (offDiagonal_determinant p.1 p.2 m m' h.2 h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2),
        m' * ((m * p.2 - 1) / (2 * p.1)))
    else (0, 1)) = (Classical.choose hexists, m' * ((m * p.2 - 1) / (2 * p.1))) := by
      rw [dif_pos hcondP]
    -- i p is that if-expression (beta); rewrite and exact hmemR
    -- i = fun p => if ..., so i p ≡ if ... (beta); hi_eq gives if ... = direct; hmemR : direct ∈ GoodR
    -- Need to show i p ∈ GoodR via hi_eq ▸ hmemR (up to beta for i p vs if ...).
    -- Use show to beta-reduce i p to if ... first.
    show ((if h : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 then
      (Classical.choose
        (offDiagonal_determinant p.1 p.2 m m' h.2 h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2),
        m' * ((m * p.2 - 1) / (2 * p.1)))
    else (0, 1))) ∈ GoodR
    rw [hi_eq]
    exact hmemR
  · -- inj on GoodL
    intro p1 hp1 p2 hp2 h_eq
    have hmemF1 := Finset.mem_filter.mp (hGoodL ▸ hp1)
    obtain ⟨hp_mem1, hcond1⟩ := hmemF1
    obtain ⟨hP1, hCE1, hCN1⟩ := hcond1
    obtain ⟨hne1, h11, h21, hd1, hd1'⟩ := hP1
    have hmemF2 := Finset.mem_filter.mp (hGoodL ▸ hp2)
    obtain ⟨hp_mem2, hcond2⟩ := hmemF2
    obtain ⟨hP2, hCE2, hCN2⟩ := hcond2
    obtain ⟨hne2, h12, h22, hd2, hd2'⟩ := hP2
    have hmemE1 : p1.1 ∈ Eset := (Finset.mem_product.mp hp_mem1).1
    have hmemE2 : p2.1 ∈ Eset := (Finset.mem_product.mp hp_mem2).1
    have he_pos1 : 0 < p1.1 := by
      have : 1 ≤ p1.1 := mem_Eset_imp_ge E p1.1 (hEset ▸ hmemE1)
      omega
    have he_pos2 : 0 < p2.1 := by
      have : 1 ≤ p2.1 := mem_Eset_imp_ge E p2.1 (hEset ▸ hmemE2)
      omega
    have hcondP1 : (m ≠ m' ∧ 1 < m * p1.2 ∧ 1 < m' * p1.2 ∧
        2 * p1.1 ∣ m * p1.2 - 1 ∧ 2 * p1.1 ∣ m' * p1.2 - 1) ∧ 0 < p1.1 :=
      ⟨⟨hne1, h11, h21, hd1, hd1'⟩, he_pos1⟩
    have hcondP2 : (m ≠ m' ∧ 1 < m * p2.2 ∧ 1 < m' * p2.2 ∧
        2 * p2.1 ∣ m * p2.2 - 1 ∧ 2 * p2.1 ∣ m' * p2.2 - 1) ∧ 0 < p2.1 :=
      ⟨⟨hne2, h12, h22, hd2, hd2'⟩, he_pos2⟩
    have hexists1 := offDiagonal_determinant p1.1 p1.2 m m' he_pos1 hne1 h11 h21 hd1 hd1'
    have hexists2 := offDiagonal_determinant p2.1 p2.2 m m' he_pos2 hne2 h12 h22 hd2 hd2'
    have hspec1 := Classical.choose_spec hexists1
    have hspec2 := Classical.choose_spec hexists2
    obtain ⟨hk_ne1, hdelta1, hincr1, hcross1⟩ := hspec1
    obtain ⟨hk_ne2, hdelta2, hincr2, hcross2⟩ := hspec2
    -- i p1 = (k1,z1), i p2 = (k2,z2) via dif_pos
    have hi_eq1 : (fun p : ℕ × ℕ =>
        if h : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
            2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 then
          (Classical.choose
            (offDiagonal_determinant p.1 p.2 m m' h.2 h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2),
            m' * ((m * p.2 - 1) / (2 * p.1)))
        else (0, 1)) p1 =
        (Classical.choose hexists1, m' * ((m * p1.2 - 1) / (2 * p1.1))) := by
      simp only [dif_pos hcondP1]
    have hi_eq2 : (fun p : ℕ × ℕ =>
        if h : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
            2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 then
          (Classical.choose
            (offDiagonal_determinant p.1 p.2 m m' h.2 h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2),
            m' * ((m * p.2 - 1) / (2 * p.1)))
        else (0, 1)) p2 =
        (Classical.choose hexists2, m' * ((m * p2.2 - 1) / (2 * p2.1))) := by
      simp only [dif_pos hcondP2]
    -- h_eq via hi_eq1/2 for inj.
    have h_pair : (Classical.choose hexists1, m' * ((m * p1.2 - 1) / (2 * p1.1))) =
        (Classical.choose hexists2, m' * ((m * p2.2 - 1) / (2 * p2.1))) :=
      hi_eq1.symm.trans (h_eq.trans hi_eq2)
    have hk12 : Classical.choose hexists1 = Classical.choose hexists2 :=
      congrArg Prod.fst h_pair
    have hz12 : m' * ((m * p1.2 - 1) / (2 * p1.1)) =
        m' * ((m * p2.2 - 1) / (2 * p2.1)) :=
      congrArg Prod.snd h_pair
    have he_eq : p1.1 = p2.1 := by
      have h_eq_int : 2 * ((p1.1 : ℕ) : ℤ) * Classical.choose hexists1 =
          2 * ((p2.1 : ℕ) : ℤ) * Classical.choose hexists1 := by
        calc 2 * ((p1.1 : ℕ) : ℤ) * Classical.choose hexists1
            = ((m' : ℕ) : ℤ) - m := hdelta1.symm
          _ = 2 * ((p2.1 : ℕ) : ℤ) * Classical.choose hexists2 := hdelta2
          _ = 2 * ((p2.1 : ℕ) : ℤ) * Classical.choose hexists1 := by rw [← hk12]
      have h2 : 2 * ((p1.1 : ℕ) : ℤ) = 2 * ((p2.1 : ℕ) : ℤ) :=
        mul_right_cancel₀ hk_ne1 h_eq_int
      have h3 : ((p1.1 : ℕ) : ℤ) = ((p2.1 : ℕ) : ℤ) :=
        mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2
      exact_mod_cast h3
    have hn_eq : p1.2 = p2.2 := by
      have hh_eq : (m * p1.2 - 1) / (2 * p1.1) = (m * p2.2 - 1) / (2 * p2.1) :=
        Nat.mul_left_cancel hm'_pos hz12
      have hmn1 : m * p1.2 = 2 * p1.1 * ((m * p1.2 - 1) / (2 * p1.1)) + 1 :=
        quotient_factor_equation p1.1 m p1.2 h11 hd1
      have hmn2 : m * p2.2 = 2 * p2.1 * ((m * p2.2 - 1) / (2 * p2.1)) + 1 :=
        quotient_factor_equation p2.1 m p2.2 h12 hd2
      have hmn_eq : m * p1.2 = m * p2.2 := by
        calc m * p1.2 = 2 * p1.1 * ((m * p1.2 - 1) / (2 * p1.1)) + 1 := hmn1
          _ = 2 * p2.1 * ((m * p2.2 - 1) / (2 * p2.1)) + 1 := by rw [hh_eq, he_eq]
          _ = m * p2.2 := hmn2.symm
      exact Nat.mul_left_cancel hm_pos hmn_eq
    exact Prod.ext he_eq hn_eq
  · -- surj from GoodR via reverse e/n.
    intro q hq
    have hmemF := Finset.mem_filter.mp (hGoodR ▸ hq)
    obtain ⟨hq_mem, hcond⟩ := hmemF
    obtain ⟨hQ, hDE, hDN⟩ := hcond
    obtain ⟨hk_ne, hzk_pos, hdvd1, hdvd2, hmod⟩ := hQ
    have hqK : q.1 ∈ Kset := (Finset.mem_product.mp hq_mem).1
    have hqZ : q.2 ∈ Zset := (Finset.mem_product.mp hq_mem).2
    -- reverse e via first cutoff + ModEq.
    obtain ⟨e, he_pos, hdelta_e, heR, he_min, he_le⟩ :=
      rev_e_exists m m' q.1 E emin etae hk_ne hE hemin hmod hsupE hDE
    -- reverse h,h' via dvd + positivity.
    have hz_pos : 0 < q.2 := by
      have : 1 ≤ q.2 := (Finset.mem_Icc.mp (hZset ▸ hqZ)).1
      omega
    have hzk_toNat_pos : 0 < (((q.2 : ℕ) : ℤ) + q.1).toNat := by
      have h2 : (0 : ℤ) ≤ ((q.2 : ℕ) : ℤ) + q.1 := le_of_lt hzk_pos
      have h3 : ((((((q.2 : ℕ) : ℤ) + q.1).toNat : ℕ)) : ℤ) =
          ((q.2 : ℕ) : ℤ) + q.1 :=
        Int.toNat_of_nonneg h2
      have h4 : (0 : ℤ) < (((((q.2 : ℕ) : ℤ) + q.1).toNat : ℕ) : ℤ) := by
        rw [h3]; exact hzk_pos
      exact_mod_cast h4
    obtain ⟨hh_pos, hh'_pos, hz_eq, hzk_eq⟩ :=
      rev_h_eq m m' q.2 q.1 hm'_pos hm_pos hz_pos hzk_toNat_pos hdvd1 hdvd2
    -- hcross via rev_hcross.
    have hcross_rev : (m : ℤ) * (((((q.2 : ℕ) : ℤ) + q.1).toNat / m : ℕ) : ℤ) -
        (m' : ℤ) * ((q.2 / m' : ℕ) : ℤ) = q.1 :=
      rev_hcross m m' (q.2 / m') ((((q.2 : ℕ) : ℤ) + q.1).toNat / m) q.2 q.1
        hz_eq hzk_eq hzk_pos
    -- coprime via rough + k small.
    have hkle_y : ((q.1.natAbs : ℕ) : ℝ) ≤ y :=
      k_natAbs_le_y M y q.1 (hKset ▸ hqK) hy
    have hcop : Nat.Coprime m q.1.natAbs :=
      rough_coprime_natAbs y m q.1 (hrough m ham) hk_ne hkle_y
    -- n via converse (unique).
    obtain ⟨n, hn, hn_uniq⟩ :=
      determinant_converse_nat m m' e (q.2 / m')
        ((((q.2 : ℕ) : ℤ) + q.1).toNat / m) q.1 hm_pos he_pos hh_pos
        hdelta_e hcross_rev hcop
    obtain ⟨hn_pos, hmn_eq, hmn'_eq⟩ := hn
    -- e ∈ Eset via emin≤e≤2E + 0<e.
    have he_mem : e ∈ Eset := by
      have h1 : 1 ≤ e := Nat.succ_le_iff.mpr he_pos
      have h2 : e ≤ ⌊2 * E⌋₊ := Nat.le_floor he_le
      rw [hEset]
      exact Finset.mem_Icc.mpr ⟨h1, h2⟩
    -- S = n/V via fwd_etan_eq with reverse e,h,n.
    have hVpos : 0 < V := by linarith
    have hVne : V ≠ 0 := ne_of_gt hVpos
    have hS_eq : (((m' : ℝ) - m) * q.2 / (q.1 * m * m' * V) + 1 / (m * V)) =
        ((n : ℝ) / V) :=
      fwd_etan_eq m m' e (q.2 / m') n q.1 V q.2 hk_ne hm_pos hm'_pos hVne
        hdelta_e hz_eq hmn_eq
    -- n ∈ Nset via S=n/V + support.
    have hn_mem : n ∈ Nset := by
      have hCN' : etan ((n : ℝ) / V) ≠ 0 := by
        rw [← hS_eq]
        exact hDN
      have hb := etan_ne_zero_imp_bounds etan ((n : ℝ) / V) hsupN hCN'
      have hle : (n : ℝ) ≤ 4 * V := by
        have : (n : ℝ) / V ≤ 4 := hb.2
        rwa [div_le_iff₀ hVpos] at this
      have h1 : 1 ≤ n := Nat.succ_le_iff.mpr hn_pos
      have h2 : n ≤ ⌊4 * V⌋₊ := Nat.le_floor hle
      rw [hNset]
      exact Finset.mem_Icc.mpr ⟨h1, h2⟩
    -- P for (e,n) via m*n=2*e*h+1 etc.
    have hP_en : m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
        2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 := by
      have h1lt : 1 < m * n := by
        have hpos : 0 < 2 * e * (q.2 / m') := Nat.mul_pos (Nat.mul_pos (by omega) he_pos) hh_pos
        omega
      have h2lt : 1 < m' * n := by
        have hpos : 0 < 2 * e * ((((q.2 : ℕ) : ℤ) + q.1).toNat / m) := by
          have : 0 < ((((q.2 : ℕ) : ℤ) + q.1).toNat / m : ℕ) := hh'_pos
          exact Nat.mul_pos (Nat.mul_pos (by omega) he_pos) this
        omega
      have hdvd1 : 2 * e ∣ m * n - 1 := by
        have hsub : m * n - 1 = 2 * e * (q.2 / m') := by omega
        rw [hsub]
        exact dvd_mul_right (2 * e) _
      have hdvd2 : 2 * e ∣ m' * n - 1 := by
        have hsub : m' * n - 1 = 2 * e * ((((q.2 : ℕ) : ℤ) + q.1).toNat / m) := by omega
        rw [hsub]
        exact dvd_mul_right (2 * e) _
      exact ⟨hne, h1lt, h2lt, hdvd1, hdvd2⟩
    -- cutoffs nonzero for (e,n) via fwd equalities + hDE/hDN.
    have hCE_en : etae ((e : ℝ) / E) ≠ 0 := by
      have heq : ((e : ℝ) / E) = (((m' : ℝ) - m) / (2 * q.1 * E)) := by
        rw [heR]
        field_simp
      rw [heq]
      exact hDE
    have hCN_en : etan ((n : ℝ) / V) ≠ 0 := by
      rw [← hS_eq]
      exact hDN
    -- (e,n) ∈ GoodL via product + P + cutoffs.
    have hmemProd_en : (e, n) ∈ Eset ×ˢ Nset :=
      Finset.mem_product.mpr ⟨he_mem, hn_mem⟩
    have hcond_en : ((m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
        2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1) ∧
      etae ((e : ℝ) / E) ≠ 0 ∧ etan ((n : ℝ) / V) ≠ 0) :=
      ⟨hP_en, hCE_en, hCN_en⟩
    have hmemL_en : (e, n) ∈ GoodL := by
      rw [hGoodL]
      exact Finset.mem_filter.mpr ⟨hmemProd_en, hcond_en⟩
    -- i (e,n) = (k,z) via dif_pos + cancel (k'=k, z'=z).
    have hi_eq_en : (fun p : ℕ × ℕ =>
        if h : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
            2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 then
          (Classical.choose
            (offDiagonal_determinant p.1 p.2 m m' h.2 h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2),
            m' * ((m * p.2 - 1) / (2 * p.1)))
        else (0, 1)) (e, n) = q := by
      have hcond_en : (m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1) ∧ 0 < e :=
        ⟨hP_en, he_pos⟩
      have hexists_en := offDiagonal_determinant e n m m' he_pos hP_en.1 hP_en.2.1 hP_en.2.2.1
        hP_en.2.2.2.1 hP_en.2.2.2.2
      have hspec_en := Classical.choose_spec hexists_en
      obtain ⟨hk_ne_en, hdelta_en, hincr_en, hcross_en⟩ := hspec_en
      -- k' = k via 2*e*k' = 2*e*k with 2*e≠0.
      have hk_eq : Classical.choose hexists_en = q.1 := by
        have h1 : 2 * ((e : ℕ) : ℤ) * Classical.choose hexists_en =
            2 * ((e : ℕ) : ℤ) * q.1 := by
          calc 2 * ((e : ℕ) : ℤ) * Classical.choose hexists_en
              = ((m' : ℕ) : ℤ) - m := hdelta_en.symm
            _ = 2 * ((e : ℕ) : ℤ) * q.1 := hdelta_e
        have hne : (2 : ℤ) * ((e : ℕ) : ℤ) ≠ 0 := by
          have he_ne : ((e : ℕ) : ℤ) ≠ 0 := by exact_mod_cast he_pos.ne'
          exact mul_ne_zero (by norm_num) he_ne
        exact mul_left_cancel₀ hne h1
      have hz_eq_en : m' * ((m * n - 1) / (2 * e)) = q.2 := by
        have hdiv_eq : (m * n - 1) / (2 * e) = q.2 / m' := by
          have hsub : m * n - 1 = 2 * e * (q.2 / m') := by omega
          have hpos2e : 0 < 2 * e := by omega
          calc (m * n - 1) / (2 * e) = (2 * e * (q.2 / m')) / (2 * e) := by rw [hsub]
            _ = q.2 / m' := Nat.mul_div_cancel_left _ hpos2e
        rw [hdiv_eq]
        exact hz_eq.symm
      have hi_eq : (fun p : ℕ × ℕ =>
          if h : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
              2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 then
            (Classical.choose
              (offDiagonal_determinant p.1 p.2 m m' h.2 h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2),
              m' * ((m * p.2 - 1) / (2 * p.1)))
          else (0, 1)) (e, n) =
          (Classical.choose hexists_en, m' * ((m * n - 1) / (2 * e))) := by
        have hcond_en' : (m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1) ∧ 0 < e :=
          ⟨hP_en, he_pos⟩
        simp only [dif_pos hcond_en']
      rw [hi_eq, hk_eq, hz_eq_en]
    exact ⟨(e, n), hmemL_en, hi_eq_en⟩
  · -- value: f(p) = g(i p) via forward cutoff/ah matching.
    intro p hp
    have hmemF := Finset.mem_filter.mp (hGoodL ▸ hp)
    obtain ⟨hp_mem, hcond⟩ := hmemF
    obtain ⟨hP, hCE, hCN⟩ := hcond
    obtain ⟨hne', h1, h2, hd, hd'⟩ := hP
    have hmemE : p.1 ∈ Eset := (Finset.mem_product.mp hp_mem).1
    have he_pos : 0 < p.1 := by
      have : 1 ≤ p.1 := mem_Eset_imp_ge E p.1 (hEset ▸ hmemE)
      omega
    have hcondP : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 :=
      ⟨⟨hne', h1, h2, hd, hd'⟩, he_pos⟩
    have hexists := offDiagonal_determinant p.1 p.2 m m' he_pos hne' h1 h2 hd hd'
    have hspec := Classical.choose_spec hexists
    obtain ⟨hk_ne, hdelta, hincr, hcross⟩ := hspec
    have hmn : m * p.2 = 2 * p.1 * ((m * p.2 - 1) / (2 * p.1)) + 1 :=
      quotient_factor_equation p.1 m p.2 h1 hd
    have hmn' : m' * p.2 = 2 * p.1 * ((m' * p.2 - 1) / (2 * p.1)) + 1 :=
      quotient_factor_equation p.1 m' p.2 h2 hd'
    -- f(p) with P true.
    have hf_eq : (if m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1 then
      (((etae ((p.1 : ℝ) / E) * etan ((p.2 : ℝ) / V) : ℝ) : ℂ)) *
        (alpha m * ah ((m * p.2 - 1) / (2 * p.1)) *
          star (alpha m' * ah ((m' * p.2 - 1) / (2 * p.1))))
    else 0) =
      (((etae ((p.1 : ℝ) / E) * etan ((p.2 : ℝ) / V) : ℝ) : ℂ)) *
        (alpha m * ah ((m * p.2 - 1) / (2 * p.1)) *
          star (alpha m' * ah ((m' * p.2 - 1) / (2 * p.1)))) := by
      rw [if_pos ⟨hne', h1, h2, hd, hd'⟩]
    -- Q for explicit forward (k,z).
    have hh'_pos : 0 < (m' * p.2 - 1) / (2 * p.1) :=
      quotient_factor_pos p.1 m' p.2 he_pos h2 hd'
    have hz_eq_int : ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
        Classical.choose hexists = (m : ℤ) * (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by
      have h1 : ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) =
          (m' : ℤ) * (((m * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by push_cast; ring
      rw [h1]
      linarith [hcross]
    have hpos_mh' : (0 : ℤ) < (m : ℤ) * (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by
      have hm_pos_int : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm_pos
      have hh'_pos_int : (0 : ℤ) < (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by
        exact_mod_cast hh'_pos
      exact mul_pos hm_pos_int hh'_pos_int
    have hQ : Classical.choose hexists ≠ 0 ∧
        0 < ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) + Classical.choose hexists ∧
        m' ∣ m' * ((m * p.2 - 1) / (2 * p.1)) ∧
        m ∣ (((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists).toNat ∧
        Nat.ModEq (2 * (Classical.choose hexists).natAbs) m m' := by
      refine ⟨hk_ne, ?_, dvd_mul_right m' _, ?_, forward_modEq m m' p.1 _ hdelta⟩
      · rw [hz_eq_int]; exact hpos_mh'
      · have hzk_pos : (0 : ℤ) < ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
            Classical.choose hexists := by rw [hz_eq_int]; exact hpos_mh'
        have htoNat_eq : (((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
            Classical.choose hexists).toNat = m * ((m' * p.2 - 1) / (2 * p.1)) := by
          have hcast_mh' : (((m * ((m' * p.2 - 1) / (2 * p.1)) : ℕ)) : ℤ) =
              (m : ℤ) * (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by push_cast; ring
          have hzk_nonneg : (0 : ℤ) ≤ ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists := le_of_lt hzk_pos
          have htoNat : (((((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists).toNat : ℕ) : ℤ) =
              ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists :=
            Int.toNat_of_nonneg hzk_nonneg
          have hcast_eq : (((((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists).toNat : ℕ) : ℤ) =
              (((m * ((m' * p.2 - 1) / (2 * p.1)) : ℕ)) : ℤ) := by
            rw [htoNat, hz_eq_int, ← hcast_mh']
          exact Int.ofNat_inj.mp hcast_eq
        rw [htoNat_eq]
        exact dvd_mul_right m _
    have hEne : E ≠ 0 := ne_of_gt hE
    have hVpos : 0 < V := by linarith
    have hVne : V ≠ 0 := ne_of_gt hVpos
    have hDE : etae (((m' : ℝ) - m) / (2 * Classical.choose hexists * E)) ≠ 0 := by
      have heq := fwd_cutoff_eq m m' p.1 (Classical.choose hexists) E hk_ne hEne hdelta
      rw [heq]
      exact hCE
    have hDN : etan (((m' : ℝ) - m) * ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℝ) /
        (Classical.choose hexists * m * m' * V) + 1 / (m * V)) ≠ 0 := by
      have heq := fwd_etan_eq m m' p.1 ((m * p.2 - 1) / (2 * p.1)) p.2
        (Classical.choose hexists) V (m' * ((m * p.2 - 1) / (2 * p.1)))
        hk_ne hm_pos hm'_pos hVne hdelta rfl hmn
      rw [heq]
      exact hCN
    have i_eq : (if h : (m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
            2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1) ∧ 0 < p.1 then
          (Classical.choose
            (offDiagonal_determinant p.1 p.2 m m' h.2 h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2),
            m' * ((m * p.2 - 1) / (2 * p.1)))
        else (0, 1))
        = (Classical.choose hexists, m' * ((m * p.2 - 1) / (2 * p.1))) :=
      dif_pos hcondP
    have hecut := fwd_cutoff_eq m m' p.1 (Classical.choose hexists) E hk_ne hEne hdelta
    have hnut := fwd_etan_eq m m' p.1 ((m * p.2 - 1) / (2 * p.1)) p.2
      (Classical.choose hexists) V (m' * ((m * p.2 - 1) / (2 * p.1)))
      hk_ne hm_pos hm'_pos hVne hdelta rfl hmn
    have ah1 : (m' * ((m * p.2 - 1) / (2 * p.1))) / m' = (m * p.2 - 1) / (2 * p.1) :=
      Nat.mul_div_cancel_left _ hm'_pos
    have htoNat_eq2 : (((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
        Classical.choose hexists).toNat = m * ((m' * p.2 - 1) / (2 * p.1)) := by
      have hcast_mh' : (((m * ((m' * p.2 - 1) / (2 * p.1)) : ℕ)) : ℤ) =
          (m : ℤ) * (((m' * p.2 - 1) / (2 * p.1) : ℕ) : ℤ) := by push_cast; ring
      have hzk_pos : (0 : ℤ) < ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists := by rw [hz_eq_int]; exact hpos_mh'
      have hzk_nonneg : (0 : ℤ) ≤ ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists := le_of_lt hzk_pos
      have htoNat : (((((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists).toNat : ℕ) : ℤ) =
          ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists :=
        Int.toNat_of_nonneg hzk_nonneg
      have hcast_eq : (((((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
          Classical.choose hexists).toNat : ℕ) : ℤ) =
          (((m * ((m' * p.2 - 1) / (2 * p.1)) : ℕ)) : ℤ) := by
        rw [htoNat, hz_eq_int, ← hcast_mh']
      exact Int.ofNat_inj.mp hcast_eq
    have ah2 : ((((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
        Classical.choose hexists).toNat / m) = (m' * p.2 - 1) / (2 * p.1) := by
      rw [htoNat_eq2]
      exact Nat.mul_div_cancel_left _ hm_pos
    rw [i_eq]
    show (if m ≠ m' ∧ 1 < m * p.2 ∧ 1 < m' * p.2 ∧
        2 * p.1 ∣ m * p.2 - 1 ∧ 2 * p.1 ∣ m' * p.2 - 1 then
      (((etae ((p.1 : ℝ) / E) * etan ((p.2 : ℝ) / V) : ℝ) : ℂ)) *
        (alpha m * ah ((m * p.2 - 1) / (2 * p.1)) *
          star (alpha m' * ah ((m' * p.2 - 1) / (2 * p.1))))
    else 0) =
      (if Classical.choose hexists ≠ 0 ∧
          0 < ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) + Classical.choose hexists ∧
          m' ∣ m' * ((m * p.2 - 1) / (2 * p.1)) ∧
          m ∣ (((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
            Classical.choose hexists).toNat ∧
          Nat.ModEq (2 * (Classical.choose hexists).natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * Classical.choose hexists * E)) *
          etan (((m' : ℝ) - m) * ((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℝ) /
            (Classical.choose hexists * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah ((m' * ((m * p.2 - 1) / (2 * p.1))) / m')) *
            star (alpha m' * ah (((((m' * ((m * p.2 - 1) / (2 * p.1)) : ℕ) : ℤ) +
              Classical.choose hexists).toNat / m))))
      else 0)
    rw [hf_eq, if_pos hQ, hecut, hnut, ah1, ah2]

/-- Per-pair equality: diagonal case `m = m'`, both double sums vanish.
LHS guard `m ≠ m'` is false; RHS cutoff `etae 0 = 0` kills every term. -/
theorem per_pair_diag (M : ℕ) (E U V emin : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) (m m' : ℕ)
    (hE : 0 < E) (hemin : 0 < emin)
    (hsupE : Function.support etae ⊆ Set.Icc (emin / E) 2)
    (hm_eq : m = m') :
    (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
        (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e))))
      else 0) =
    (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
      else 0) := by
  subst hm_eq
  have hL : (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      if m ≠ m ∧ 1 < m * n ∧ 1 < m * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m * n - 1 then
        (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m * ah ((m * n - 1) / (2 * e))))
      else 0) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    apply Finset.sum_eq_zero; intro n _
    have hneg : ¬(m ≠ m ∧ 1 < m * n ∧ 1 < m * n ∧
        2 * e ∣ m * n - 1 ∧ 2 * e ∣ m * n - 1) := fun h => h.1 rfl
    rw [if_neg hneg]
  have hR : (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m then
        ((etae (((m : ℝ) - m) / (2 * k * E)) *
          etan (((m : ℝ) - m) * z / (k * m * m * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m)) * star (alpha m * ah (((z : ℤ) + k).toNat / m)))
      else 0) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro z _
    by_cases hQ : k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
        Nat.ModEq (2 * k.natAbs) m m
    · rw [if_pos hQ]
      have harg : (((m : ℝ) - m) / (2 * (k : ℝ) * E)) = 0 := by simp [sub_self]
      rw [harg, etae_zero_of_diag emin E hE hemin etae hsupE, zero_mul,
        Complex.ofReal_zero, zero_mul]
    · rw [if_neg hQ]
  rw [hL, hR]

/-- Per-pair equality when `alpha m = 0`: both arith factors vanish. -/
theorem per_pair_alphaL (M : ℕ) (E U V emin : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) (m m' : ℕ) (ham0 : alpha m = 0) :
    (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
        (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e))))
      else 0) =
    (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
      else 0) := by
  have hL0 : (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
        (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e))))
      else 0) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    apply Finset.sum_eq_zero; intro n _
    by_cases hP : m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
        2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1
    · rw [if_pos hP]; simp [ham0]
    · rw [if_neg hP]
  have hR0 : (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
      else 0) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro z _
    by_cases hQ : k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
        Nat.ModEq (2 * k.natAbs) m m'
    · rw [if_pos hQ]; simp [ham0]
    · rw [if_neg hQ]
  rw [hL0, hR0]

/-- Per-pair equality when `alpha m' = 0`: both `star` factors vanish. -/
theorem per_pair_alphaR (M : ℕ) (E U V emin : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) (m m' : ℕ) (ham0' : alpha m' = 0) :
    (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
        (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e))))
      else 0) =
    (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
      else 0) := by
  have hL0 : (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
        (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e))))
      else 0) = 0 := by
    apply Finset.sum_eq_zero; intro e _
    apply Finset.sum_eq_zero; intro n _
    by_cases hP : m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
        2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1
    · rw [if_pos hP]; simp [ham0']
    · rw [if_neg hP]
  have hR0 : (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
      else 0) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro z _
    by_cases hQ : k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
        Nat.ModEq (2 * k.natAbs) m m'
    · rw [if_pos hQ]; simp [ham0']
    · rw [if_neg hQ]
  rw [hL0, hR0]

/-- Reshuffle the literal sum to `m,m'`-outer form. -/
theorem reshuffle_LHS (E U V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ) :
    offDiagonalSum E U V etae etan ah alpha =
    ∑ m ∈ dyad U, ∑ m' ∈ dyad U, ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊,
      ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
          2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
        (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
          (alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e))))
      else 0 := by
  have step0 : ∀ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∀ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
      (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
        (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
          if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
              2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
            alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e)))
          else 0) =
      ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0 :=
    fun e _ n _ => offDiagonal_inner_eq E U V etae etan ah alpha e n
  have stepA : (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0)
      = (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ m ∈ dyad U, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0) := by
    apply Finset.sum_congr rfl; intro e _
    exact Finset.sum_comm
  have stepB : (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ m ∈ dyad U, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0)
      = (∑ m ∈ dyad U, ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0) :=
    Finset.sum_comm
  have stepC : ∀ m ∈ dyad U,
      (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0)
      = (∑ m' ∈ dyad U, ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0) := by
    intro m _
    have e1 : (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
          ∑ m' ∈ dyad U,
          if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
              2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
            (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
              (alpha m * ah ((m * n - 1) / (2 * e)) *
                star (alpha m' * ah ((m' * n - 1) / (2 * e))))
          else 0)
        = ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ m' ∈ dyad U, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
          if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
              2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
            (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
              (alpha m * ah ((m * n - 1) / (2 * e)) *
                star (alpha m' * ah ((m' * n - 1) / (2 * e))))
          else 0 := by
      apply Finset.sum_congr rfl; intro e _
      exact Finset.sum_comm
    have e2 : (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ m' ∈ dyad U, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
          if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
              2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
            (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
              (alpha m * ah ((m * n - 1) / (2 * e)) *
                star (alpha m' * ah ((m' * n - 1) / (2 * e))))
          else 0)
        = ∑ m' ∈ dyad U, ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
          if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
              2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
            (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
              (alpha m * ah ((m * n - 1) / (2 * e)) *
                star (alpha m' * ah ((m' * n - 1) / (2 * e))))
          else 0 := Finset.sum_comm
    exact e1.trans e2
  calc offDiagonalSum E U V etae etan ah alpha
      = (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0) := by
        unfold offDiagonalSum
        apply Finset.sum_congr rfl; intro e he
        apply Finset.sum_congr rfl; intro n hn
        exact step0 e he n hn
    _ = (∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ m ∈ dyad U, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0) := stepA
    _ = (∑ m ∈ dyad U, ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0) := stepB
    _ = (∑ m ∈ dyad U, ∑ m' ∈ dyad U, ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          (((etae ((e : ℝ) / E) * etan ((n : ℝ) / V) : ℝ) : ℂ)) *
            (alpha m * ah ((m * n - 1) / (2 * e)) *
              star (alpha m' * ah ((m' * n - 1) / (2 * e))))
        else 0) := by
        apply Finset.sum_congr rfl; intro m hm
        exact stepC m hm

/-- Reshuffle the determinant sum to `m,m'`-outer form, bridging the
association `(↑X * A) * S = ↑X * (A * S)` of the copied summand. -/
theorem reshuffle_RHS (M : ℕ) (E U V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ) :
    determinantSum M (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊) E U V etae etan ah alpha =
    ∑ m ∈ dyad U, ∑ m' ∈ dyad U, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
      else 0 := by
  have assocR : ∀ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      ∀ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
      ∀ m ∈ dyad U, ∀ m' ∈ dyad U,
      (if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        (etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) *
          (alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m))
      else 0)
      = (if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        ((etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
          ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
      else 0) := by
    intro k _ z _ m _ m' _
    by_cases hQ : k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
        Nat.ModEq (2 * k.natAbs) m m'
    · rw [if_pos hQ, if_pos hQ, mul_assoc]
    · rw [if_neg hQ, if_neg hQ]
  have stepA : (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
        ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0)
      = (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ m ∈ dyad U,
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊), ∑ m' ∈ dyad U,
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0) := by
    apply Finset.sum_congr rfl; intro k _
    exact Finset.sum_comm
  have stepB : (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ m ∈ dyad U,
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊), ∑ m' ∈ dyad U,
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0)
      = (∑ m ∈ dyad U, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊), ∑ m' ∈ dyad U,
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0) :=
    Finset.sum_comm
  have stepC : ∀ m ∈ dyad U,
      (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊), ∑ m' ∈ dyad U,
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0)
      = (∑ m' ∈ dyad U, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0) := by
    intro m _
    have e1 : (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊), ∑ m' ∈ dyad U,
          if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
              Nat.ModEq (2 * k.natAbs) m m' then
            ((etae (((m' : ℝ) - m) / (2 * k * E)) *
              etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
              ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
          else 0)
        = ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ m' ∈ dyad U,
          ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
          if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
              Nat.ModEq (2 * k.natAbs) m m' then
            ((etae (((m' : ℝ) - m) / (2 * k * E)) *
              etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
              ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
          else 0 := by
      apply Finset.sum_congr rfl; intro k _
      exact Finset.sum_comm
    have e2 : (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ m' ∈ dyad U,
          ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
          if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
              Nat.ModEq (2 * k.natAbs) m m' then
            ((etae (((m' : ℝ) - m) / (2 * k * E)) *
              etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
              ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
          else 0)
        = ∑ m' ∈ dyad U, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
          if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
              Nat.ModEq (2 * k.natAbs) m m' then
            ((etae (((m' : ℝ) - m) / (2 * k * E)) *
              etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
              ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
          else 0 := Finset.sum_comm
    exact e1.trans e2
  calc determinantSum M (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊) E U V etae etan ah alpha
      = (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
        ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0) := by
        unfold determinantSum
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro z _
        apply Finset.sum_congr rfl; intro m _
        apply Finset.sum_congr rfl; intro m' _
        exact assocR k (by assumption) z (by assumption) m (by assumption) m' (by assumption)
    _ = (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ m ∈ dyad U,
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊), ∑ m' ∈ dyad U,
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0) := stepA
    _ = (∑ m ∈ dyad U, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊), ∑ m' ∈ dyad U,
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0) := stepB
    _ = (∑ m ∈ dyad U, ∑ m' ∈ dyad U, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ z ∈ Finset.Icc 1 (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊),
        if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
            Nat.ModEq (2 * k.natAbs) m m' then
          ((etae (((m' : ℝ) - m) / (2 * k * E)) *
            etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) : ℂ) *
            ((alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m)))
        else 0) := by
        apply Finset.sum_congr rfl; intro m hm
        exact stepC m hm

/-- The finite determinant reindexing identity. -/
theorem offDiagonalReindex_proof : OffDiagonalReindexTask := by
  intro M E U V emin y etae etan ah alpha hE hU hV hemin hUM hy hrough hsupE hsupN
  have hLHS := reshuffle_LHS E U V etae etan ah alpha
  have hRHS := reshuffle_RHS M E U V etae etan ah alpha
  rw [hLHS, hRHS]
  apply Finset.sum_congr rfl; intro m hm
  apply Finset.sum_congr rfl; intro m' hm'
  by_cases hmm : m = m'
  · exact per_pair_diag M E U V emin etae etan ah alpha m m' hE hemin hsupE hmm
  · by_cases ham0 : alpha m = 0
    · exact per_pair_alphaL M E U V emin etae etan ah alpha m m' ham0
    · by_cases ham0' : alpha m' = 0
      · exact per_pair_alphaR M E U V emin etae etan ah alpha m m' ham0'
      · exact per_pair_eq_of_ne_of_alpha M E U V emin y etae etan ah alpha m m'
          hE hU hV hemin hUM hy hrough hsupE hsupN hm hm' hmm ham0 ham0'
end Main

end Erdos821.P6Reidx
