import Erdos821.P6Off.Partition

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic Erdos821.S56Core

def dyadicDeterminantSum (M N : ℕ) (E U V Z : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(M : ℤ)) M, ∑ z ∈ Finset.Icc 1 N,
    ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
      (dyadicCutoff (z / Z) : ℂ) * determinantTerm E V etae etan ah alpha k z m m'

/-- Insert the fixed finite smooth dyadic partition into the exact determinant sum. -/
theorem determinantSum_dyadic_partition (x U V K0 Cs : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) (M N : ℕ)
    (hx : 32 ≤ x) (hL : 128 ≤ L x) (hU : 0 < U) (hV : 0 < V)
    (hK : 0 < K0) (hCs : 0 < Cs)
    (hUVlo : x / 8 ≤ U * V) (hUVhi : U * V ≤ 8 * x)
    (hse : Function.support etae ⊆ Set.Icc (L x ^ (-Cs) / 2) 2)
    (hsn : Function.support etan ⊆ Set.Icc (1 / 2) 4)
    (hpart : ∀ z : ℝ, x * L x ^ (-(K0 + Cs + 1)) ≤ z →
      z ≤ x * L x ^ (K0 + Cs + 1) →
      (∑ j ∈ Finset.range (dyadicCount x (K0 + Cs + 1)),
        dyadicCutoff (z / dyadicScale x (K0 + Cs + 1) j)) = 1) :
    determinantSum M N (U * L x ^ (-K0)) U V etae etan ah alpha =
      ∑ j ∈ Finset.range (dyadicCount x (K0 + Cs + 1)),
        dyadicDeterminantSum M N (U * L x ^ (-K0)) U V
          (dyadicScale x (K0 + Cs + 1) j) etae etan ah alpha := by
  change (∑ k ∈ Finset.Icc (-(M : ℤ)) M, ∑ z ∈ Finset.Icc 1 N,
    ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
      determinantTerm (U * L x ^ (-K0)) V etae etan ah alpha k z m m') = _
  unfold dyadicDeterminantSum
  apply insert_finite_partition
  intro k _ z hz m hm m' hm' hw
  have hzpos : 0 < z := (Finset.mem_Icc.mp hz).1
  obtain ⟨hlo, hhi⟩ := determinantTerm_z_window x U V K0 Cs etae etan ah alpha hx hL
    hU hV hK hCs hUVlo hUVhi hse hsn k z m m' hzpos hm hm' hw
  exact_mod_cast hpart z hlo hhi

/-- The partition is uniform in every finite determinant truncation. -/
theorem eventually_determinantSum_dyadic_partition (K0 Cs : ℝ) (hK : 0 < K0) (hCs : 0 < Cs) :
    ∀ᶠ x : ℝ in atTop, ∀ (U V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ) (M N : ℕ),
      0 < U → 0 < V → x / 8 ≤ U * V → U * V ≤ 8 * x →
      Function.support etae ⊆ Set.Icc (L x ^ (-Cs) / 2) 2 →
      Function.support etan ⊆ Set.Icc (1 / 2) 4 →
      determinantSum M N (U * L x ^ (-K0)) U V etae etan ah alpha =
        ∑ j ∈ Finset.range (dyadicCount x (K0 + Cs + 1)),
          dyadicDeterminantSum M N (U * L x ^ (-K0)) U V
            (dyadicScale x (K0 + Cs + 1) j) etae etan ah alpha := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_dyadic_scales (K0 + Cs + 1) (by linarith),
    eventually_ge_atTop (32 : ℝ), hL.eventually (eventually_ge_atTop 128)] with x hpart hx hL128
  intro U V etae etan ah alpha M N hU hV hUVlo hUVhi hse hsn
  exact determinantSum_dyadic_partition x U V K0 Cs etae etan ah alpha M N hx hL128 hU hV hK hCs
    hUVlo hUVhi hse hsn hpart.2.2.2


end Erdos821.P6Off
