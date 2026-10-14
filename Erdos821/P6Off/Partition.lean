import Erdos821.P6Off.DyadicScales
import Erdos821.P6Off.PulledRange
import Erdos821.P6Off.ReindexTask

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- Insert a finite z partition into a finite four-variable weighted sum. -/
theorem insert_finite_partition (ks : Finset ℤ) (zs ms mts js : Finset ℕ)
    (w : ℤ → ℕ → ℕ → ℕ → ℂ) (phi : ℕ → ℕ → ℂ)
    (hpart : ∀ k ∈ ks, ∀ z ∈ zs, ∀ m ∈ ms, ∀ m' ∈ mts,
      w k z m m' ≠ 0 → (∑ j ∈ js, phi j z) = 1) :
    (∑ k ∈ ks, ∑ z ∈ zs, ∑ m ∈ ms, ∑ m' ∈ mts, w k z m m') =
      ∑ j ∈ js, ∑ k ∈ ks, ∑ z ∈ zs, ∑ m ∈ ms, ∑ m' ∈ mts,
        phi j z * w k z m m' := by
  simp_rw [Finset.sum_comm (s := js) (t := ks), Finset.sum_comm (s := js) (t := zs),
    Finset.sum_comm (s := js) (t := ms), Finset.sum_comm (s := js) (t := mts)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro m' hm'
  rw [← Finset.sum_mul]
  by_cases hw : w k z m m' = 0
  · simp [hw]
  · rw [hpart k hk z hz m hm m' hm' hw, one_mul]

/-- The literal determinant summand, with its original positivity and
integer divisibility guards. -/
def determinantTerm (E V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ)
    (k : ℤ) (z m m' : ℕ) : ℂ :=
  if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
      Nat.ModEq (2 * k.natAbs) m m' then
    (etae (((m' : ℝ) - m) / (2 * k * E)) *
      etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) *
      (alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m))
  else 0

theorem determinantTerm_z_window (x U V K0 Cs : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ)
    (hx : 32 ≤ x) (hL : 128 ≤ L x) (hU : 0 < U) (hV : 0 < V)
    (hK : 0 < K0) (hCs : 0 < Cs)
    (hUVlo : x / 8 ≤ U * V) (hUVhi : U * V ≤ 8 * x)
    (hse : Function.support etae ⊆ Set.Icc (L x ^ (-Cs) / 2) 2)
    (hsn : Function.support etan ⊆ Set.Icc (1 / 2) 4)
    (k : ℤ) (z m m' : ℕ) (hz : 0 < z) (hm : m ∈ dyad U) (hm' : m' ∈ dyad U)
    (hw : determinantTerm (U * L x ^ (-K0)) V etae etan ah alpha k z m m' ≠ 0) :
    x * L x ^ (-(K0 + Cs + 1)) ≤ (z : ℝ) ∧ (z : ℝ) ≤ x * L x ^ (K0 + Cs + 1) := by
  unfold determinantTerm at hw
  split_ifs at hw with hguard
  · have hweight : etae (((m' : ℝ) - m) / (2 * k * (U * L x ^ (-K0)))) *
        etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) ≠ 0 := by
      intro hzero
      apply hw
      rw [hzero]
      simp
    have hmR := (mem_dyad_iff U m).mp hm
    have hm'R := (mem_dyad_iff U m').mp hm'
    exact pulled_cutoff_z_range x U V K0 Cs etae etan hx hL hU hV hK hCs hUVlo hUVhi
      hse hsn k hguard.1 m m' z (by exact_mod_cast hz) ⟨hmR.1, hmR.2.le⟩
      ⟨hm'R.1, hm'R.2.le⟩ hweight
  · exact False.elim (hw rfl)


end Erdos821.P6Off
