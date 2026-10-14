import Erdos821.Blueprint.TypeII

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P6Mass
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Finite tilted marked harmonic mass, uniform in the truncation N. The
one-group Euler expansion uses aₚ=(p^(1-θ)-1)⁻¹, θ=L^(-d), aₚ≤2e/p;
the product over O(T) groups is a fixed power of L. This avoids a summability
obligation in the consuming Type II tail argument. -/
def TiltedGroupMassTask : Prop :=
  ∀ P : Geometry, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
    ∀ G : PrimeGroups, Admissible P x G → ∀ N : ℕ,
      (∑ v ∈ Finset.Icc 1 N,
        if groupFreePart G v = 1 then
          markWeight G P.q (fun _ => P.ell) v /
            (v : ℝ) ^ (1 - L x ^ (-P.d))
        else 0) ≤ L x ^ C

end Erdos821.P6Mass

namespace Erdos821.P6Mass
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Log-threshold from which all analytic estimates hold. Depends only on `P`. -/
def thresh (P : Geometry) : ℝ :=
  max 2 (max (Real.exp (Real.log 7 / P.a)) (Real.exp 1))

lemma thresh_ge_two (P : Geometry) : 2 ≤ thresh P := le_max_left _ _

lemma thresh_pos (P : Geometry) : 0 < thresh P :=
  lt_of_lt_of_le (by norm_num) (thresh_ge_two P)

/-- `L x` exceeds the threshold once `x ≥ exp thresh`. -/
lemma L_ge_thresh_of_ge {P : Geometry} {x : ℝ} (hx : Real.exp (thresh P) ≤ x) :
    thresh P ≤ L x := by
  unfold L
  have hpos : 0 < Real.exp (thresh P) := Real.exp_pos _
  have hxpos : 0 < x := lt_of_lt_of_le hpos hx
  have h := Real.log_le_log hpos hx
  rwa [Real.log_exp] at h

lemma L_gt_one_of_ge {P : Geometry} {x : ℝ} (hx : Real.exp (thresh P) ≤ x) :
    1 < L x :=
  lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (thresh_ge_two P)) (L_ge_thresh_of_ge hx)

lemma L_pos_of_ge {P : Geometry} {x : ℝ} (hx : Real.exp (thresh P) ≤ x) :
    0 < L x := lt_trans zero_lt_one (L_gt_one_of_ge hx)

lemma T_pos_of_ge {P : Geometry} {x : ℝ} (hx : Real.exp (thresh P) ≤ x) :
    0 < T x := by
  unfold T
  exact Real.log_pos (L_gt_one_of_ge hx)

lemma geom_a_pos (P : Geometry) : 0 < P.a := P.ordered.1
lemma geom_a_lt_b (P : Geometry) : P.a < P.b := P.ordered.2.1
lemma geom_b_lt_c (P : Geometry) : P.b < P.c := P.ordered.2.2.1
lemma geom_c_lt_d (P : Geometry) : P.c < P.d := P.ordered.2.2.2.1
lemma geom_d_lt (P : Geometry) : P.d < 0.47 := P.ordered.2.2.2.2
lemma geom_d_pos (P : Geometry) : 0 < P.d := by
  have h1 := geom_a_pos P; have h2 := geom_a_lt_b P
  have h3 := geom_b_lt_c P; have h4 := geom_c_lt_d P
  linarith
lemma geom_c_pos (P : Geometry) : 0 < P.c := by
  have := geom_a_pos P; have := geom_a_lt_b P; have := geom_b_lt_c P; linarith
lemma geom_b_pos (P : Geometry) : 0 < P.b := by
  have := geom_a_pos P; have := geom_a_lt_b P; linarith
lemma geom_c0_pos (P : Geometry) : 0 < P.c₀ := P.positive.1
lemma geom_C0_pos (P : Geometry) : 0 < P.C₀ := P.positive.2.1
lemma geom_vmin_pos (P : Geometry) : 0 < P.vmin := P.positive.2.2.1
lemma geom_vmin_le_vmax (P : Geometry) : P.vmin ≤ P.vmax := P.positive.2.2.2
lemma geom_q_pos (P : Geometry) : 0 < P.q := P.damping.1
lemma geom_q_lt_one (P : Geometry) : P.q < 1 := P.damping.2
lemma geom_ell_pos (P : Geometry) : 1 ≤ P.ell := P.marks

/-- For `L ≥ thresh`, `L ^ a ≥ 7`. -/
lemma rpow_a_ge_seven {P : Geometry} {x : ℝ} (hx : Real.exp (thresh P) ≤ x) :
    7 ≤ L x ^ P.a := by
  have hL := L_pos_of_ge hx
  have ha := geom_a_pos P
  have hth : Real.exp (Real.log 7 / P.a) ≤ L x := by
    have h1 : Real.exp (Real.log 7 / P.a) ≤ thresh P :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans h1 (L_ge_thresh_of_ge hx)
  have hlog : Real.log 7 / P.a ≤ Real.log (L x) := by
    have hpos : 0 < Real.exp (Real.log 7 / P.a) := Real.exp_pos _
    have h := Real.log_le_log hpos hth
    rwa [Real.log_exp] at h
  have hmul : Real.log 7 ≤ Real.log (L x) * P.a := by
    have hdiv := (div_le_iff₀ ha).mp hlog
    linarith [mul_comm (Real.log (L x)) P.a]
  have hrpow : L x ^ P.a = Real.exp (Real.log (L x) * P.a) :=
    Real.rpow_def_of_pos hL _
  rw [hrpow]
  have hexp : Real.exp (Real.log 7) ≤ Real.exp (Real.log (L x) * P.a) :=
    Real.exp_le_exp.mpr hmul
  rwa [Real.exp_log (by norm_num : (0:ℝ) < 7)] at hexp

/-- Tilt parameter `θ = L ^ (-d)`. -/
def theta (P : Geometry) (x : ℝ) : ℝ := L x ^ (-P.d)

lemma theta_pos {P : Geometry} {x : ℝ} (hx : Real.exp (thresh P) ≤ x) :
    0 < theta P x :=
  Real.rpow_pos_of_pos (L_pos_of_ge hx) _

lemma theta_lt_one {P : Geometry} {x : ℝ} (hx : Real.exp (thresh P) ≤ x) :
    theta P x < 1 := by
  unfold theta
  have hL1 : 1 < L x := L_gt_one_of_ge hx
  have hd := geom_d_pos P
  have hLd : 1 < L x ^ P.d := Real.one_lt_rpow hL1 hd
  have hpos : 0 < L x ^ P.d := Real.rpow_pos_of_pos (L_pos_of_ge hx) _
  rw [Real.rpow_neg (le_of_lt (L_pos_of_ge hx))]
  rw [inv_lt_one_iff₀]
  exact Or.inr hLd

lemma one_sub_theta_pos {P : Geometry} {x : ℝ}
    (hx : Real.exp (thresh P) ≤ x) : 0 < 1 - theta P x := by
  have := theta_lt_one (P := P) hx
  have := theta_pos (P := P) hx
  linarith

/-- Every group prime is at least `exp (L ^ a)`, hence at least 7. -/
lemma prime_ge_exp_a {P : Geometry} {x G : _} {g : Fin G.size} {p : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G)
    (hmem : p ∈ G.primes g) : Real.exp (L x ^ P.a) ≤ (p : ℝ) := by
  have h4 := hG.2.2.2.1 g p hmem
  by_cases hg : g ∈ G.small
  · rw [if_pos hg] at h4
    exact h4.1
  · rw [if_neg hg] at h4
    have hac : P.a < P.c := lt_trans (geom_a_lt_b P) (geom_b_lt_c P)
    have hL1 : 1 < L x := L_gt_one_of_ge hx
    have hpow : L x ^ P.a ≤ L x ^ P.c :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hL1) (le_of_lt hac)
    exact le_trans (Real.exp_le_exp.mpr hpow) h4.1

lemma prime_ge_seven {P : Geometry} {x G : _} {g : Fin G.size} {p : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G)
    (hmem : p ∈ G.primes g) : 7 ≤ (p : ℝ) := by
  have h1 := prime_ge_exp_a hx hG hmem
  have hLa : (7:ℝ) ≤ L x ^ P.a := rpow_a_ge_seven hx
  have hexp7 : (7:ℝ) ≤ Real.exp 7 := by
    have h := Real.add_one_le_exp (7:ℝ)
    linarith
  have h2 : Real.exp 7 ≤ Real.exp (L x ^ P.a) := Real.exp_le_exp.mpr hLa
  exact le_trans (le_trans hexp7 h2) h1

/-- Every group prime is at most `exp (L ^ d)`. -/
lemma prime_le_exp_d {P : Geometry} {x G : _} {g : Fin G.size} {p : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G)
    (hmem : p ∈ G.primes g) : (p : ℝ) ≤ Real.exp (L x ^ P.d) := by
  have h4 := hG.2.2.2.1 g p hmem
  have hL1 : 1 < L x := L_gt_one_of_ge hx
  by_cases hg : g ∈ G.small
  · rw [if_pos hg] at h4
    have hbd : P.b < P.d :=
      lt_trans (geom_b_lt_c P) (geom_c_lt_d P)
    have hpow : L x ^ P.b ≤ L x ^ P.d :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hL1) (le_of_lt hbd)
    exact le_trans h4.2 (Real.exp_le_exp.mpr hpow)
  · rw [if_neg hg] at h4
    exact h4.2

lemma prime_pos_cast {G : PrimeGroups} {g : Fin G.size} {p : ℕ}
    (hmem : p ∈ G.primes g) : (0:ℝ) < (p : ℝ) := by
  have hprime := G.prime g p hmem
  have h2 : 2 ≤ p := hprime.two_le
  have : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
  linarith

/-- `log p ≤ L ^ d` for every group prime. -/
lemma log_prime_le {P : Geometry} {x G : _} {g : Fin G.size} {p : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G)
    (hmem : p ∈ G.primes g) : Real.log (p : ℝ) ≤ L x ^ P.d := by
  have hpos : (0:ℝ) < (p : ℝ) := prime_pos_cast hmem
  have hle := prime_le_exp_d hx hG hmem
  have h := Real.log_le_log hpos hle
  rwa [Real.log_exp] at h

/-- `p ^ θ ≤ e` for every group prime. -/
lemma rpow_prime_theta_le {P : Geometry} {x G : _} {g : Fin G.size} {p : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G)
    (hmem : p ∈ G.primes g) : (p : ℝ) ^ theta P x ≤ Real.exp 1 := by
  have hpos : (0:ℝ) < (p : ℝ) := prime_pos_cast hmem
  have hlog := log_prime_le hx hG hmem
  have htheta := theta_pos (P := P) hx
  have hLpos := L_pos_of_ge hx
  have hd := geom_d_pos P
  have hLd_pos : 0 < L x ^ P.d := Real.rpow_pos_of_pos hLpos _
  -- θ * log p ≤ 1
  have hbound : theta P x * Real.log (p : ℝ) ≤ 1 := by
    unfold theta
    have h1 : L x ^ (-P.d) * (L x ^ P.d) = 1 := by
      rw [← Real.rpow_add hLpos]
      simp [neg_add_cancel]
    have h2 : L x ^ (-P.d) * Real.log (p : ℝ) ≤ L x ^ (-P.d) * (L x ^ P.d) := by
      apply mul_le_mul_of_nonneg_left hlog (le_of_lt (Real.rpow_pos_of_pos hLpos _))
    rw [h1] at h2
    exact h2
  have hrpow : (p : ℝ) ^ theta P x = Real.exp (Real.log (p : ℝ) * theta P x) :=
    Real.rpow_def_of_pos hpos _
  rw [hrpow]
  have : Real.log (p : ℝ) * theta P x ≤ 1 := by
    rw [mul_comm]; exact hbound
  exact Real.exp_le_exp.mpr this

/-- Tilted Euler factor `a_p = (p ^ (1-θ) - 1)⁻¹`. -/
def ap (P : Geometry) (x : ℝ) (p : ℕ) : ℝ :=
  (((p : ℝ) ^ (1 - theta P x) - 1))⁻¹

lemma ap_pos {P : Geometry} {x : ℝ} {p : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hp2 : 2 ≤ (p : ℝ)) :
    0 < ap P x p := by
  unfold ap
  have hLpos := L_pos_of_ge hx
  have htheta := theta_lt_one (P := P) hx
  have hs_pos : 0 < (1:ℝ) - theta P x := one_sub_theta_pos hx
  have hppos : (0:ℝ) < (p : ℝ) := by linarith
  have h1 : (1:ℝ) < (p : ℝ) ^ (1 - theta P x) := by
    have hbase : (1:ℝ) < (p : ℝ) := by linarith
    exact Real.one_lt_rpow hbase hs_pos
  have : (0:ℝ) < (p : ℝ) ^ (1 - theta P x) - 1 := by linarith
  exact inv_pos.mpr this

lemma pow_one_sub_theta_eq {P : Geometry} {x : ℝ} {p : ℕ}
    (hppos : (0:ℝ) < (p : ℝ)) :
    (p : ℝ) ^ (1 - theta P x) = (p : ℝ) / (p : ℝ) ^ theta P x := by
  have h1 : (p : ℝ) ^ (1:ℝ) / (p : ℝ) ^ theta P x = (p : ℝ) ^ (1 - theta P x) := by
    rw [← Real.rpow_sub hppos]
  rw [Real.rpow_one] at h1
  exact h1.symm

/-- `a_p ≤ 2e / p` eventually, uniformly over group primes. -/
lemma ap_le {P : Geometry} {x G : _} {g : Fin G.size} {p : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G)
    (hmem : p ∈ G.primes g) : ap P x p ≤ 2 * Real.exp 1 / (p : ℝ) := by
  have hp7 : (7:ℝ) ≤ (p : ℝ) := prime_ge_seven hx hG hmem
  have hppos : (0:ℝ) < (p : ℝ) := prime_pos_cast hmem
  have hptheta : (p : ℝ) ^ theta P x ≤ Real.exp 1 :=
    rpow_prime_theta_le hx hG hmem
  have hptheta_pos : (0:ℝ) < (p : ℝ) ^ theta P x :=
    Real.rpow_pos_of_pos hppos _
  have hepos : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  have hpow_eq := pow_one_sub_theta_eq (P := P) (x := x) hppos
  -- 2e ≤ p
  have hp2e : 2 * Real.exp 1 ≤ (p : ℝ) := by
    have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have h2e_pos : (0:ℝ) < 2 * Real.exp 1 := by positivity
  -- p / p^θ ≥ p / e
  have hge : (p : ℝ) / Real.exp 1 ≤ (p : ℝ) / (p : ℝ) ^ theta P x := by
    apply div_le_div_of_nonneg_left (le_of_lt hppos) hptheta_pos hptheta
  -- p / e - 1 ≥ p / (2e)
  have hsub : (p : ℝ) / (2 * Real.exp 1) ≤ (p : ℝ) / Real.exp 1 - 1 := by
    have hsplit : (p : ℝ) / Real.exp 1
        = (p : ℝ) / (2 * Real.exp 1) + (p : ℝ) / (2 * Real.exp 1) := by
      field_simp
      ring
    rw [hsplit]
    have hone : (1:ℝ) ≤ (p : ℝ) / (2 * Real.exp 1) := by
      rw [le_div_iff₀ h2e_pos]
      linarith
    linarith
  have hs_ge : (p : ℝ) / (2 * Real.exp 1) ≤ (p : ℝ) ^ (1 - theta P x) - 1 := by
    rw [hpow_eq]
    exact le_trans hsub (by linarith [hge])
  have hs_pos : (0:ℝ) < (p : ℝ) / (2 * Real.exp 1) :=
    div_pos hppos h2e_pos
  have hs1_pos : (0:ℝ) < (p : ℝ) ^ (1 - theta P x) - 1 :=
    lt_of_lt_of_le hs_pos hs_ge
  have hle : (((p : ℝ) ^ (1 - theta P x) - 1))⁻¹ ≤ ((p : ℝ) / (2 * Real.exp 1))⁻¹ :=
    (inv_le_inv₀ hs1_pos hs_pos).mpr hs_ge
  have hinv : ((p : ℝ) / (2 * Real.exp 1))⁻¹ = 2 * Real.exp 1 / (p : ℝ) := by
    rw [inv_div]
  rw [hinv] at hle
  unfold ap
  exact hle

lemma mass_nonneg (G : PrimeGroups) (g : Fin G.size) : 0 ≤ mass G g := by
  unfold mass
  apply Finset.sum_nonneg
  intro p _
  positivity

lemma mass_le_vmax {P : Geometry} {x : ℝ} {G : PrimeGroups} (hG : Admissible P x G)
    (g : Fin G.size) : mass G g ≤ P.vmax :=
  (hG.2.2.1 g).2

lemma mass_ge_vmin {P : Geometry} {x : ℝ} {G : PrimeGroups} (hG : Admissible P x G)
    (g : Fin G.size) : P.vmin ≤ mass G g :=
  (hG.2.2.1 g).1

lemma mass_pos_of_adm {P : Geometry} {x : ℝ} {G : PrimeGroups} (hG : Admissible P x G)
    (g : Fin G.size) : 0 < mass G g :=
  lt_of_lt_of_le (geom_vmin_pos P) (mass_ge_vmin hG g)

/-- `∑ a_p ≤ 2e * V`. -/
lemma sum_ap_le {P : Geometry} {x : ℝ} {G : PrimeGroups} {g : Fin G.size}
    (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G) :
    ∑ p ∈ G.primes g, ap P x p ≤ 2 * Real.exp 1 * mass G g := by
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hmem
  have h := ap_le hx hG hmem
  rw [mul_one_div]
  exact h

lemma sum_ap_le_vmax {P : Geometry} {x : ℝ} {G : PrimeGroups} {g : Fin G.size}
    (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G) :
    ∑ p ∈ G.primes g, ap P x p ≤ 2 * Real.exp 1 * P.vmax := by
  have h1 := sum_ap_le hx hG (g := g)
  have h2 := mass_le_vmax hG g
  have hepos : (0:ℝ) ≤ 2 * Real.exp 1 := by positivity
  exact le_trans h1 (by apply mul_le_mul_of_nonneg_left h2 hepos)

lemma ap_nonneg {P : Geometry} {x : ℝ} {p : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hp2 : 2 ≤ (p : ℝ)) : 0 ≤ ap P x p :=
  le_of_lt (ap_pos hx hp2)

/-- Range geometric sum `∑_{i<n} r^i ≤ (1-r)⁻¹` for `0 ≤ r < 1`. -/
lemma range_geom_le {r : ℝ} {n : ℕ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ _i ∈ Finset.range n, r ^ _i ≤ (1 - r)⁻¹ := by
  have hrne : r ≠ 1 := ne_of_lt hr1
  have heq := geom_sum_eq hrne n
  have h1r : (0:ℝ) < 1 - r := by linarith
  have hpow_nonneg : (0:ℝ) ≤ r ^ n := pow_nonneg hr0 n
  have hle : (1:ℝ) - r ^ n ≤ 1 := by linarith
  have hdiv : (1 - r ^ n) / (1 - r) ≤ 1 / (1 - r) := by
    apply div_le_div_of_nonneg_right hle (le_of_lt h1r)
  have heq2 : (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) := by
    have h1 : r ^ n - 1 = - (1 - r ^ n) := by ring
    have h2 : r - 1 = - (1 - r) := by ring
    rw [h1, h2, neg_div_neg_eq]
  rw [heq, heq2]
  have hone : (1:ℝ) / (1 - r) = (1 - r)⁻¹ := one_div _
  rw [hone] at hdiv
  exact hdiv

/-- Finite geometric row `∑_{e=1..M} r^e ≤ r / (1-r)` for `0 ≤ r < 1`. -/
lemma geom_row_le {r : ℝ} {M : ℕ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ e ∈ Finset.Icc 1 M, r ^ e ≤ r / (1 - r) := by
  by_cases hM : M = 0
  · simp [hM]
    apply div_nonneg hr0
    linarith
  · have h1r : (0:ℝ) < 1 - r := by linarith
    -- range (M+1) = {0} ∪ Icc 1 M
    have hmem0 : (0:ℕ) ∈ Finset.range (M + 1) := Finset.mem_range.mpr (Nat.succ_pos M)
    have herase : (Finset.range (M + 1)).erase 0 = Finset.Icc 1 M := by
      ext e
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc, ne_eq]
      constructor
      · intro h
        have hlt : e < M + 1 := h.2
        have hne : e ≠ 0 := h.1
        have h1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr hne
        have h2 : e ≤ M := Nat.lt_succ_iff.mp hlt
        exact ⟨h1, h2⟩
      · intro h
        exact ⟨by omega, by omega⟩
    have hsum_range := range_geom_le hr0 hr1 (n := M + 1)
    have hsum_erase : r ^ (0:ℕ) + ∑ e ∈ (Finset.range (M + 1)).erase 0, r ^ e
        = ∑ e ∈ Finset.range (M + 1), r ^ e :=
      Finset.add_sum_erase _ _ hmem0
    simp only [pow_zero] at hsum_erase
    rw [herase] at hsum_erase
    have hIcc_le : ∑ e ∈ Finset.Icc 1 M, r ^ e ≤ (1 - r)⁻¹ - 1 := by linarith
    have heq : r / (1 - r) = (1 - r)⁻¹ - 1 := by
      field_simp
      ring
    rw [heq]
    exact hIcc_le

/-- `∑_{e=1..M} p^{-e·s} ≤ a_p`. -/
lemma pow_row_le_ap {P : Geometry} {x : ℝ} {p : ℕ} {M : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hp2 : 2 ≤ (p : ℝ)) :
    ∑ e ∈ Finset.Icc 1 M, (((p : ℝ) ^ (1 - theta P x))⁻¹) ^ e ≤ ap P x p := by
  have hLpos := L_pos_of_ge hx
  have hs_pos : 0 < (1:ℝ) - theta P x := one_sub_theta_pos hx
  have hppos : (0:ℝ) < (p : ℝ) := by linarith
  have hPs : (1:ℝ) < (p : ℝ) ^ (1 - theta P x) := by
    exact Real.one_lt_rpow (by linarith) hs_pos
  have hPs_pos : (0:ℝ) < (p : ℝ) ^ (1 - theta P x) := by linarith
  have hr0 : (0:ℝ) ≤ (((p : ℝ) ^ (1 - theta P x))⁻¹) := le_of_lt (inv_pos.mpr hPs_pos)
  have hr1 : (((p : ℝ) ^ (1 - theta P x))⁻¹) < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hPs
  have hrow := geom_row_le hr0 hr1 (M := M)
  have heq : ap P x p = (((p : ℝ) ^ (1 - theta P x))⁻¹) / (1 - (((p : ℝ) ^ (1 - theta P x))⁻¹)) := by
    unfold ap
    field_simp
  rw [heq]
  exact hrow

/-- `M₀(P) = ∑' t, t^ℓ q^t`, the uniform polynomial-times-geometric bound. -/
def M0 (P : Geometry) : ℝ := ∑' t : ℕ, (t : ℝ) ^ P.ell * P.q ^ t

lemma summable_M0 (P : Geometry) : Summable (fun t : ℕ => (t : ℝ) ^ P.ell * P.q ^ t) := by
  have hq1 : P.q < 1 := geom_q_lt_one P
  have hnorm : ‖P.q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (geom_q_pos P)]
    exact hq1
  exact summable_pow_mul_geometric_of_norm_lt_one P.ell hnorm

lemma M0_nonneg (P : Geometry) : 0 ≤ M0 P := by
  unfold M0
  apply tsum_nonneg
  intro t
  apply mul_nonneg
  · apply pow_nonneg
    positivity
  · apply pow_nonneg
    exact le_of_lt (geom_q_pos P)

lemma M0_pos (P : Geometry) : 0 < M0 P := by
  have hsumm := summable_M0 P
  have h1 : (1:ℝ) ^ P.ell * P.q ^ (1:ℕ) ≤ M0 P := by
    unfold M0
    have h := hsumm.sum_le_tsum ({1} : Finset ℕ)
      (fun i _ => by
        apply mul_nonneg
        · apply pow_nonneg; positivity
        · apply pow_nonneg; exact le_of_lt (geom_q_pos P))
    simpa using h
  simp only [one_pow, one_mul] at h1
  have hq := geom_q_pos P
  linarith

/-- Each `t^ℓ q^t ≤ M₀`. -/
lemma pow_mul_le_M0 (P : Geometry) (t : ℕ) :
    (t : ℝ) ^ P.ell * P.q ^ t ≤ M0 P := by
  unfold M0
  have hsumm := summable_M0 P
  have h := hsumm.sum_le_tsum ({t} : Finset ℕ)
    (fun i _ => by
      apply mul_nonneg
      · apply pow_nonneg; positivity
      · apply pow_nonneg; exact le_of_lt (geom_q_pos P))
  simpa using h

/-- Per-group constant `K₀`, depending only on `P`. -/
def K0 (P : Geometry) : ℝ :=
  M0 P * Real.exp (2 * Real.exp 1 * P.vmax) / (P.q ^ P.ell * P.vmin ^ P.ell)

lemma K0_pos (P : Geometry) : 0 < K0 P := by
  unfold K0
  have hM0 := M0_pos P
  have hexp : (0:ℝ) < Real.exp (2 * Real.exp 1 * P.vmax) := Real.exp_pos _
  have hq : (0:ℝ) < P.q ^ P.ell := pow_pos (geom_q_pos P) _
  have hvmin := geom_vmin_pos P
  have hv : (0:ℝ) < P.vmin ^ P.ell := pow_pos hvmin _
  positivity

/-- Global exponent `C`, depending only on `P`. -/
def Cmass (P : Geometry) : ℝ := max 0 (2 * P.C₀ * Real.log (K0 P))

lemma Cmass_nonneg (P : Geometry) : 0 ≤ Cmass P := le_max_left _ _

/-- Group support: primes of `g` dividing `w`. -/
def gsupp (G : PrimeGroups) (g : Fin G.size) (w : ℕ) : Finset ℕ :=
  (G.primes g).filter (· ∣ w)

lemma gsupp_card_eq (G : PrimeGroups) (g : Fin G.size) (w : ℕ) :
    (gsupp G g w).card = omegaGroup G g w := rfl

lemma markWeight_nonneg (P : Geometry) (G : PrimeGroups) (w : ℕ)
    (hq : 0 < P.q) : 0 ≤ markWeight G P.q (fun _ => P.ell) w := by
  unfold markWeight
  apply mul_nonneg
  · apply le_of_lt
    apply zpow_pos hq
  · apply Finset.prod_nonneg
    intro g _
    apply div_nonneg
    · positivity
    · apply pow_nonneg
      apply mass_nonneg

/-- `q ^ (∑ s) = ∏ q ^ s` for `q ≠ 0`. -/
lemma zpow_sum_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) {q : ℝ}
    (hq : q ≠ 0) :
    q ^ (∑ i ∈ s, f i) = ∏ i ∈ s, q ^ f i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq, ih]

/-- `(∏ a) ^ s = ∏ a ^ s` for nonneg `a`, real `s`. -/
lemma rpow_prod_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (r : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ r = ∏ i ∈ s, (f i) ^ r := by
  induction s using Finset.induction with
  | empty => simp [Real.one_rpow]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    rw [Real.mul_rpow (hf a (Finset.mem_insert_self a s))
      (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- `(d : ℝ) ≤ (t : ℝ)^ℓ` where `d = descFactorial`. -/
lemma desc_cast_le (t ell : ℕ) :
    (Nat.descFactorial t ell : ℝ) ≤ (t : ℝ) ^ ell := by
  have h := Nat.descFactorial_le_pow t ell
  exact_mod_cast h

/-- Uniform mark-factor bound. -/
lemma mark_factor_le (P : Geometry) (t : ℕ) :
    (Nat.descFactorial t P.ell : ℝ) * P.q ^ ((t : ℤ) - (P.ell : ℤ))
      ≤ M0 P / P.q ^ P.ell := by
  have hq := geom_q_pos P
  have hqell : (0:ℝ) < P.q ^ P.ell := pow_pos hq _
  have hM0 := M0_nonneg P
  have hRHS_nonneg : (0:ℝ) ≤ M0 P / P.q ^ P.ell :=
    div_nonneg hM0 (le_of_lt hqell)
  by_cases ht : t < P.ell
  · have hdesc : Nat.descFactorial t P.ell = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr ht
    rw [hdesc, Nat.cast_zero, zero_mul]
    exact hRHS_nonneg
  · push_neg at ht
    have hsub : ((t : ℤ) - (P.ell : ℤ)) = ((t - P.ell : ℕ) : ℤ) := by
      rw [Nat.cast_sub ht]
    have hpow_eq : P.q ^ ((t : ℤ) - (P.ell : ℤ))
        = P.q ^ t / P.q ^ P.ell := by
      rw [hsub, zpow_natCast]
      have ht_eq : t = (t - P.ell) + P.ell := (Nat.sub_add_cancel ht).symm
      have hmul : P.q ^ t = P.q ^ (t - P.ell) * P.q ^ P.ell := by
        nth_rewrite 1 [ht_eq]
        rw [pow_add]
      exact eq_div_of_mul_eq (ne_of_gt hqell) hmul.symm
    rw [hpow_eq]
    have hdesc_le : (Nat.descFactorial t P.ell : ℝ) ≤ (t : ℝ) ^ P.ell :=
      desc_cast_le t P.ell
    have hqt_nonneg : (0:ℝ) ≤ P.q ^ t := pow_nonneg (le_of_lt hq) _
    have hmul : (Nat.descFactorial t P.ell : ℝ) * P.q ^ t
        ≤ (t : ℝ) ^ P.ell * P.q ^ t :=
      mul_le_mul_of_nonneg_right hdesc_le hqt_nonneg
    have hM0_le := pow_mul_le_M0 P t
    have h1 : (Nat.descFactorial t P.ell : ℝ) * P.q ^ t ≤ M0 P :=
      le_trans hmul hM0_le
    have : (Nat.descFactorial t P.ell : ℝ) * (P.q ^ t / P.q ^ P.ell)
        ≤ M0 P / P.q ^ P.ell := by
      rw [← mul_div_assoc]
      have h2 : (Nat.descFactorial t P.ell : ℝ) * P.q ^ t / P.q ^ P.ell
          ≤ M0 P / P.q ^ P.ell :=
        div_le_div_of_nonneg_right h1 (le_of_lt hqell)
      -- `div_le_div_of_nonneg_right` signature? Check: it might be
      -- `div_le_div_right`? Use `div_le_div_right` with positivity.
      -- Fall back to `gcongr` if needed.
      exact h2
    exact this

/-- Exponent `e = factorization` lies in `Icc 0 N` when `w ∈ Icc 1 N`
and `p^{e} ∣ w` with `p ≥ 2`. -/
lemma expo_le_of_mem {w p N : ℕ} (hw1 : 1 ≤ w) (hwN : w ≤ N)
    (hp2 : 2 ≤ p) (e : ℕ) (hdvd : p ^ e ∣ w) : e ≤ N := by
  by_cases he0 : e = 0
  · omega
  · have h2e_dvd : 2 ^ e ≤ w := by
      have h2e_le_pe : 2 ^ e ≤ p ^ e := pow_le_pow_left₀ (by norm_num) hp2 e
      exact le_trans h2e_le_pe (Nat.le_of_dvd (by omega) hdvd)
    have hlt : e < 2 ^ e := Nat.lt_two_pow_self
    omega

/-- `((p ^ e) : ℝ) ^ s = ((p : ℝ) ^ s) ^ e` for `p > 0`. -/
lemma rpow_pow_comm {p : ℝ} {e : ℕ} {s : ℝ} (hp : 0 < p) :
    ((p ^ e : ℝ)) ^ s = ((p ^ s : ℝ)) ^ e := by
  have h1 : ((p ^ e : ℝ)) ^ s = p ^ ((e : ℝ) * s) := by
    have hcast : ((p ^ e : ℝ)) = p ^ ((e : ℝ)) := by
      rw [Real.rpow_natCast]
    rw [hcast, ← Real.rpow_mul (le_of_lt hp)]
  have h2 : ((p ^ s : ℝ)) ^ e = p ^ (s * (e : ℝ)) := by
    have hcast : (((p ^ s : ℝ)) ^ e : ℝ) = (p ^ s) ^ ((e : ℝ)) := by
      rw [Real.rpow_natCast]
    rw [hcast, ← Real.rpow_mul (le_of_lt hp)]
  rw [h1, h2, mul_comm ((e : ℝ)) s]

/-- Harmonic atom `g_p(e) = 1 / ((p^e : ℝ) ^ s)`, nonneg. -/
def harmAtom (p : ℕ) (s : ℝ) (e : ℕ) : ℝ := 1 / (((p ^ e : ℕ) : ℝ) ^ s)

lemma harmAtom_nonneg (p : ℕ) (s : ℝ) (e : ℕ) : 0 ≤ harmAtom p s e := by
  unfold harmAtom
  apply div_nonneg zero_le_one
  apply Real.rpow_nonneg
  positivity

lemma harmAtom_zero (p : ℕ) (s : ℝ) : harmAtom p s 0 = 1 := by
  unfold harmAtom
  simp [Real.one_rpow]

/-- `harmAtom p s e = (((p : ℝ) ^ s)⁻¹) ^ e` for `p ≥ 2`. -/
lemma harmAtom_eq {p : ℕ} {s : ℝ} {e : ℕ} (hp2 : 2 ≤ p) :
    harmAtom p s e = (((p : ℝ) ^ s)⁻¹) ^ e := by
  unfold harmAtom
  have hppos : (0:ℝ) < (p : ℝ) := by
    have : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hcast : (((p ^ e : ℕ) : ℝ)) = (p : ℝ) ^ e := by
    exact_mod_cast rfl
  rw [hcast]
  have hcomm : (((p : ℝ) ^ e) ^ s) = (((p : ℝ) ^ s) ^ e) := rpow_pow_comm hppos
  rw [hcomm, one_div, inv_pow]

/-- Row `∑_{e=0..N} harmAtom ≤ 1 + a_p` for group primes. -/
lemma harm_row_le {P : Geometry} {x : ℝ} {p : ℕ} {N : ℕ}
    (hx : Real.exp (thresh P) ≤ x) (hp2 : 2 ≤ p)
    (hp7 : 7 ≤ (p : ℝ)) :
    ∑ e ∈ Finset.Icc 0 N, harmAtom p (1 - theta P x) e ≤ 1 + ap P x p := by
  have h0_not : (0:ℕ) ∉ Finset.Icc 1 N := by simp
  have hIcc_eq : Finset.Icc 0 N = insert (0:ℕ) (Finset.Icc 1 N) := by
    ext e
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hIcc_eq, Finset.sum_insert h0_not, harmAtom_zero]
  have hsum_eq : ∑ e ∈ Finset.Icc 1 N, harmAtom p (1 - theta P x) e
      = ∑ e ∈ Finset.Icc 1 N, ((((p : ℝ) ^ (1 - theta P x))⁻¹) ^ e) := by
    apply Finset.sum_congr rfl
    intro e _
    exact harmAtom_eq hp2
  rw [hsum_eq]
  have hle := pow_row_le_ap (P := P) hx (p := p) (M := N) (by
    have : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith)
  linarith

/-- `∏ (1 + y) ≤ exp (∑ y)` for `y ≥ 0`. -/
lemma prod_one_add_le_exp {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ)
    (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∏ i ∈ s, (1 + y i) ≤ Real.exp (∑ i ∈ s, y i) := by
  have h1 : ∏ i ∈ s, (1 + y i) ≤ ∏ i ∈ s, Real.exp (y i) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      have := hy i hi
      linarith
    · intro i hi
      have := Real.add_one_le_exp (y i)
      linarith
  have h2 : ∏ i ∈ s, Real.exp (y i) = Real.exp (∑ i ∈ s, y i) := by
    rw [Real.exp_sum]
  rw [h2] at h1
  exact h1

/-- Per-group tilted factor. -/
def pgF (P : Geometry) (x : ℝ) (G : PrimeGroups) (g : Fin G.size) (w : ℕ) : ℝ :=
  ((Nat.descFactorial (omegaGroup G g w) P.ell : ℝ)
      * P.q ^ (((omegaGroup G g w : ℤ) - (P.ell : ℤ)))
      / mass G g ^ P.ell) / ((w : ℝ) ^ (1 - theta P x))

/-- `w = ∏_{p∈Pr} p^{e_p}` when `primeFactors ⊆ Pr` and `w ≥ 1`. -/
lemma w_eq_prod_primes {w : ℕ} {Pr : Finset ℕ} (hw1 : 1 ≤ w)
    (hsub : w.primeFactors ⊆ Pr) :
    w = ∏ p ∈ Pr, p ^ w.factorization p := by
  have hw0 : w ≠ 0 := by omega
  have hsupp : w.factorization.support = w.primeFactors :=
    Nat.support_factorization w
  have hw_eq : w.factorization.prod (· ^ ·) = w :=
    Nat.prod_factorization_pow_eq_self hw0
  have hprod_eq : (∏ p ∈ w.factorization.support, p ^ w.factorization p) = w := by
    have h := hw_eq
    simp only [Finsupp.prod] at h
    exact h
  rw [hsupp] at hprod_eq
  -- `∏_{primeFactors} = w`, extend to `Pr` via subset (extra factors 1)
  have hext : ∏ p ∈ w.primeFactors, p ^ w.factorization p
      = ∏ p ∈ Pr, p ^ w.factorization p := by
    apply Finset.prod_subset hsub
    intro p hmemPr hmemNot
    have hfact0 : w.factorization p = 0 := by
      have : p ∉ w.factorization.support := by
        rw [hsupp]
        exact hmemNot
      exact Finsupp.notMem_support_iff.mp this
    rw [hfact0, pow_zero]
  rw [← hext]
  exact hprod_eq.symm

/-- `1 / (w:ℝ)^s = ∏_{p∈Pr} harmAtom p s (e_p)` under same hypotheses,
with `s` real, `e_p = factorization`. -/
lemma inv_rpow_eq_prod_harm {w : ℕ} {Pr : Finset ℕ} (hw1 : 1 ≤ w)
    (hsub : w.primeFactors ⊆ Pr) (s : ℝ) :
    1 / ((w : ℝ) ^ s) = ∏ p ∈ Pr, harmAtom p s (w.factorization p) := by
  have hw_eq := w_eq_prod_primes hw1 hsub
  have hcast : ((w : ℝ)) = ∏ p ∈ Pr, (((p ^ w.factorization p : ℕ) : ℝ)) := by
    conv_lhs => rw [hw_eq]
    rw [Nat.cast_prod]
  have hrpow : ((w : ℝ) ^ s) = ∏ p ∈ Pr, ((((p ^ w.factorization p : ℕ) : ℝ)) ^ s) := by
    rw [hcast]
    apply rpow_prod_eq
    intro p _
    positivity
  have hprod_inv : (∏ p ∈ Pr, ((((p ^ w.factorization p : ℕ) : ℝ)) ^ s))⁻¹
      = ∏ p ∈ Pr, ((((p ^ w.factorization p : ℕ) : ℝ)) ^ s)⁻¹ := by
    rw [Finset.prod_inv_distrib]
  have hone : (1:ℝ) / ((w : ℝ) ^ s) = (((w : ℝ) ^ s))⁻¹ := one_div _
  rw [hone, hrpow, hprod_inv]
  apply Finset.prod_congr rfl
  intro p _
  unfold harmAtom
  rw [one_div]

/-- Per-group harmonic sum `∑_{w} 1/w^s ≤ exp(2e·vmax)` via direct pi-product. -/
lemma harm_sum_le {P : Geometry} {x : ℝ} {G : PrimeGroups} {g : Fin G.size}
    {N : ℕ} (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G) :
    ∑ w ∈ (Finset.Icc 1 N).filter (fun w => w.primeFactors ⊆ G.primes g),
      1 / ((w : ℝ) ^ (1 - theta P x)) ≤ Real.exp (2 * Real.exp 1 * P.vmax) := by
  -- Direct pi-product: `S=(Icc1N).filter primeFactors⊆Pr`, `E=Pr.pi(Icc0N)`,
  -- `w↦e_w` with `e_w(a)=factorization`, `F(w)=∏harmAtom` via `inv_rpow_eq`,
  -- injection via `eq_of_factorization_eq` (outside 0 via subset + support),
  -- `∑_S=∑_image≤∑_E=∏∑≤∏(1+a_p)≤exp` via `prod_sum` + `attach` + rows.
  set Pr := G.primes g with hPr
  set ss : ℝ := 1 - theta P x with hss
  set S := (Finset.Icc 1 N).filter (fun w => w.primeFactors ⊆ Pr) with hS
  set E := Pr.pi (fun _ => Finset.Icc 0 N) with hE
  -- `∑_S ≤ ∏_{Pr}(1+a_p)` via pi-injection + `prod_sum`, then `∏≤exp`.
  have hprod_le : ∑ w ∈ S, 1 / ((w : ℝ) ^ ss) ≤ ∏ p ∈ Pr, (1 + ap P x p) := by
    classical
    haveI := Classical.decEq (↥Pr → ℕ)
    haveI := Classical.decEq (↥Pr)
    -- Exponent tuple map `w ↦ (p ↦ e_p)`, landing in the pi-finset.
    set φ : ℕ → (↥Pr → ℕ) := fun w a => w.factorization a.val with hφ
    set Pf : Finset (↥Pr → ℕ) :=
      Fintype.piFinset (fun _ : ↥Pr => Finset.Icc 0 N) with hPf
    have hmem : ∀ w ∈ S, ∀ a : ↥Pr, φ w a ∈ Finset.Icc 0 N := by
      intro w hw a
      have hwmem := Finset.mem_filter.mp (hS ▸ hw)
      have hw1 : 1 ≤ w := (Finset.mem_Icc.mp hwmem.1).1
      have hwN : w ≤ N := (Finset.mem_Icc.mp hwmem.1).2
      have hmem' : a.val ∈ G.primes g := hPr ▸ a.property
      have hprime := G.prime g a.val hmem'
      have hp2 : 2 ≤ a.val := hprime.two_le
      have hdvd : a.val ^ w.factorization a.val ∣ w := Nat.ordProj_dvd w a.val
      have hle : w.factorization a.val ≤ N := expo_le_of_mem hw1 hwN hp2 _ hdvd
      have hshow : φ w a = w.factorization a.val := by rw [hφ]
      rw [hshow]
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hle⟩
    have hinj : Set.InjOn φ (↑S) := by
      intro a ha b hb hab
      have haS := Finset.mem_filter.mp (hS ▸ (Finset.mem_coe.mp ha))
      have hbS := Finset.mem_filter.mp (hS ▸ (Finset.mem_coe.mp hb))
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp haS.1).1
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hbS.1).1
      apply Nat.eq_of_factorization_eq (by omega) (by omega)
      intro p
      by_cases hp : p ∈ Pr
      · have hpa : φ a ⟨p, hp⟩ = φ b ⟨p, hp⟩ := congrFun hab ⟨p, hp⟩
        have e1 : φ a ⟨p, hp⟩ = a.factorization p := by rw [hφ]
        have e2 : φ b ⟨p, hp⟩ = b.factorization p := by rw [hφ]
        rw [e1] at hpa
        rw [e2] at hpa
        exact hpa
      · have ha0 : a.factorization p = 0 := by
          have hnp : p ∉ a.primeFactors := fun hcon => hp (haS.2 hcon)
          have hns : p ∉ a.factorization.support := by
            rw [Nat.support_factorization]; exact hnp
          exact Finsupp.notMem_support_iff.mp hns
        have hb0 : b.factorization p = 0 := by
          have hnp : p ∉ b.primeFactors := fun hcon => hp (hbS.2 hcon)
          have hns : p ∉ b.factorization.support := by
            rw [Nat.support_factorization]; exact hnp
          exact Finsupp.notMem_support_iff.mp hns
        rw [ha0, hb0]
    have hsum_eq : (∑ w ∈ S, (1:ℝ) / ((w : ℝ) ^ ss))
        = ∑ y ∈ S.image φ, (∏ a : ↥Pr, harmAtom (a.val) ss (y a)) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun w hw => ?_
      have hwmem := Finset.mem_filter.mp (hS ▸ hw)
      have hw1 : 1 ≤ w := (Finset.mem_Icc.mp hwmem.1).1
      have hsub : w.primeFactors ⊆ Pr := hwmem.2
      have hF := inv_rpow_eq_prod_harm hw1 hsub ss
      have hG : (∏ a : ↥Pr, harmAtom (a.val) ss (φ w a))
          = ∏ p ∈ Pr, harmAtom p ss (w.factorization p) := by
        have e : ∀ a : ↥Pr, harmAtom (a.val) ss (φ w a)
            = harmAtom (a.val) ss (w.factorization a.val) := by
          intro a
          have e1 : φ w a = w.factorization a.val := by rw [hφ]
          rw [e1]
        calc (∏ a : ↥Pr, harmAtom (a.val) ss (φ w a))
            = ∏ a : ↥Pr, harmAtom (a.val) ss (w.factorization a.val) :=
              Finset.prod_congr rfl (fun a _ => e a)
          _ = ∏ p ∈ Pr, harmAtom p ss (w.factorization p) :=
              Finset.prod_coe_sort Pr (fun p => harmAtom p ss (w.factorization p))
      rw [hF]
      exact hG.symm
    have hsub_img : S.image φ ⊆ Pf := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      rw [hPf, Fintype.mem_piFinset]
      intro a
      exact hmem w hw a
    have hnnG : ∀ y ∈ Pf, y ∉ S.image φ →
        0 ≤ ∏ a : ↥Pr, harmAtom (a.val) ss (y a) := by
      intro y _ _
      exact Finset.prod_nonneg (fun a _ => harmAtom_nonneg _ _ _)
    have hle : (∑ y ∈ S.image φ, ∏ a : ↥Pr, harmAtom (a.val) ss (y a))
        ≤ ∑ y ∈ Pf, ∏ a : ↥Pr, harmAtom (a.val) ss (y a) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_img hnnG
    have hpi : (∑ y ∈ Pf, ∏ a : ↥Pr, harmAtom (a.val) ss (y a))
        = ∏ a : ↥Pr, ∑ e ∈ Finset.Icc 0 N, harmAtom (a.val) ss e := by
      rw [hPf]
      exact (Finset.prod_univ_sum _ _).symm
    have hrow : ∀ a ∈ (Finset.univ : Finset ↥Pr),
        ∑ e ∈ Finset.Icc 0 N, harmAtom (a.val) ss e ≤ 1 + ap P x (a.val) := by
      intro a _
      have hmem' : a.val ∈ G.primes g := hPr ▸ a.property
      have hprime := G.prime g a.val hmem'
      have hp2 : 2 ≤ a.val := hprime.two_le
      have hp7 : 7 ≤ ((a.val : ℕ) : ℝ) := prime_ge_seven hx hG hmem'
      exact harm_row_le hx hp2 hp7
    have hnn_sum : ∀ a ∈ (Finset.univ : Finset ↥Pr),
        0 ≤ ∑ e ∈ Finset.Icc 0 N, harmAtom (a.val) ss e := by
      intro a _
      exact Finset.sum_nonneg (fun e _ => harmAtom_nonneg _ _ _)
    have hfin : (∏ a : ↥Pr, ∑ e ∈ Finset.Icc 0 N, harmAtom (a.val) ss e)
        ≤ ∏ a : ↥Pr, (1 + ap P x (a.val)) :=
      Finset.prod_le_prod₀ hnn_sum hrow
    have hconv : (∏ a : ↥Pr, (1 + ap P x (a.val)))
        = ∏ p ∈ Pr, (1 + ap P x p) :=
      Finset.prod_coe_sort Pr (fun p => 1 + ap P x p)
    calc ∑ w ∈ S, 1 / ((w : ℝ) ^ ss)
        = ∑ y ∈ S.image φ, ∏ a : ↥Pr, harmAtom (a.val) ss (y a) := hsum_eq
      _ ≤ ∑ y ∈ Pf, ∏ a : ↥Pr, harmAtom (a.val) ss (y a) := hle
      _ = ∏ a : ↥Pr, ∑ e ∈ Finset.Icc 0 N, harmAtom (a.val) ss e := hpi
      _ ≤ ∏ a : ↥Pr, (1 + ap P x (a.val)) := hfin
      _ = ∏ p ∈ Pr, (1 + ap P x p) := hconv
  have hprod_exp : ∏ p ∈ Pr, (1 + ap P x p)
      ≤ Real.exp (2 * Real.exp 1 * P.vmax) := by
    have hap_nonneg : ∀ p ∈ Pr, 0 ≤ ap P x p := by
      intro p hmem
      have hmem' : p ∈ G.primes g := hPr ▸ hmem
      have hprime := G.prime g p hmem'
      have hp2 : 2 ≤ p := hprime.two_le
      have hp2r : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      exact ap_nonneg hx hp2r
    have h1 := prod_one_add_le_exp Pr (fun p => ap P x p)
      (fun p hmem => hap_nonneg p hmem)
    have h2 : ∑ p ∈ Pr, ap P x p ≤ 2 * Real.exp 1 * P.vmax := hPr ▸ sum_ap_le_vmax hx hG
    exact le_trans h1 (Real.exp_le_exp.mpr h2)
  exact le_trans hprod_le hprod_exp

/-- `pgF` is nonneg (numerator nonneg, `w^s ≥ 0`). -/
lemma pgF_nonneg (P : Geometry) (x : ℝ) (G : PrimeGroups) (g : Fin G.size) (w : ℕ) :
    0 ≤ pgF P x G g w := by
  unfold pgF
  apply div_nonneg
  · apply div_nonneg
    · apply mul_nonneg
      · positivity
      · exact le_of_lt (zpow_pos (geom_q_pos P) _)
    · exact pow_nonneg (mass_nonneg G g) _
  · exact Real.rpow_nonneg (Nat.cast_nonneg w) _

/-- Per-group tilted mass `∑ pgF ≤ K₀`. -/
lemma per_group_le {P : Geometry} {x : ℝ} {G : PrimeGroups} {g : Fin G.size}
    {N : ℕ} (hx : Real.exp (thresh P) ≤ x) (hG : Admissible P x G) :
    ∑ w ∈ (Finset.Icc 1 N).filter (fun w => w.primeFactors ⊆ G.primes g),
      pgF P x G g w ≤ K0 P := by
  have hq := geom_q_pos P
  have hqell : (0:ℝ) < P.q ^ P.ell := pow_pos hq _
  have hvmin := geom_vmin_pos P
  have hvminell : (0:ℝ) < P.vmin ^ P.ell := pow_pos hvmin _
  have hM0 : (0:ℝ) ≤ M0 P := M0_nonneg P
  have hC1_nonneg : (0:ℝ) ≤ M0 P / (P.q ^ P.ell * P.vmin ^ P.ell) :=
    div_nonneg hM0 (le_of_lt (mul_pos hqell hvminell))
  have hmasspos : (0:ℝ) < mass G g := mass_pos_of_adm hG g
  have hMpos : (0:ℝ) < mass G g ^ P.ell := pow_pos hmasspos _
  have hkey : ∀ w ∈ (Finset.Icc 1 N).filter
      (fun w => w.primeFactors ⊆ G.primes g),
      pgF P x G g w ≤ (M0 P / (P.q ^ P.ell * P.vmin ^ P.ell))
        * (1 / ((w : ℝ) ^ (1 - theta P x))) := by
    intro w hw
    have hw1 : 1 ≤ w := (Finset.mem_Icc.mp (Finset.mem_of_mem_filter w hw)).1
    have hwpos : (0:ℝ) < (w : ℝ) := by exact_mod_cast hw1
    have hws : (0:ℝ) < ((w : ℝ) ^ (1 - theta P x)) := Real.rpow_pos_of_pos hwpos _
    have hA : (Nat.descFactorial (omegaGroup G g w) P.ell : ℝ)
          * P.q ^ (((omegaGroup G g w : ℤ) - (P.ell : ℤ)))
          ≤ M0 P / P.q ^ P.ell :=
      mark_factor_le P (omegaGroup G g w)
    have hmass : P.vmin ≤ mass G g := mass_ge_vmin hG g
    have hB : P.vmin ^ P.ell ≤ mass G g ^ P.ell :=
      pow_le_pow_left₀ (le_of_lt hvmin) hmass _
    have hA0_nonneg : (0:ℝ) ≤ M0 P / P.q ^ P.ell :=
      div_nonneg hM0 (le_of_lt hqell)
    have hdiv : (Nat.descFactorial (omegaGroup G g w) P.ell : ℝ)
          * P.q ^ (((omegaGroup G g w : ℤ) - (P.ell : ℤ))) / mass G g ^ P.ell
          ≤ (M0 P / P.q ^ P.ell) / P.vmin ^ P.ell := by
      rw [div_le_div_iff₀ hMpos hvminell]
      calc (Nat.descFactorial (omegaGroup G g w) P.ell : ℝ)
            * P.q ^ (((omegaGroup G g w : ℤ) - (P.ell : ℤ))) * P.vmin ^ P.ell
          ≤ (M0 P / P.q ^ P.ell) * P.vmin ^ P.ell :=
            mul_le_mul_of_nonneg_right hA (le_of_lt hvminell)
        _ ≤ (M0 P / P.q ^ P.ell) * mass G g ^ P.ell :=
            mul_le_mul_of_nonneg_left hB hA0_nonneg
    have hfin : ((Nat.descFactorial (omegaGroup G g w) P.ell : ℝ)
          * P.q ^ (((omegaGroup G g w : ℤ) - (P.ell : ℤ))) / mass G g ^ P.ell)
          / ((w : ℝ) ^ (1 - theta P x))
          ≤ ((M0 P / P.q ^ P.ell) / P.vmin ^ P.ell)
          / ((w : ℝ) ^ (1 - theta P x)) :=
      div_le_div_of_nonneg_right hdiv (le_of_lt hws)
    have hC1eq : ((M0 P / P.q ^ P.ell) / P.vmin ^ P.ell)
          / ((w : ℝ) ^ (1 - theta P x))
          = (M0 P / (P.q ^ P.ell * P.vmin ^ P.ell))
          * (1 / ((w : ℝ) ^ (1 - theta P x))) := by
      have hqne : P.q ^ P.ell ≠ 0 := ne_of_gt hqell
      have hvne : P.vmin ^ P.ell ≠ 0 := ne_of_gt hvminell
      have hwne : ((w : ℝ) ^ (1 - theta P x)) ≠ 0 := ne_of_gt hws
      field_simp
    unfold pgF
    rwa [hC1eq] at hfin
  calc ∑ w ∈ (Finset.Icc 1 N).filter (fun w => w.primeFactors ⊆ G.primes g),
        pgF P x G g w
      ≤ ∑ w ∈ (Finset.Icc 1 N).filter (fun w => w.primeFactors ⊆ G.primes g),
        (M0 P / (P.q ^ P.ell * P.vmin ^ P.ell))
        * (1 / ((w : ℝ) ^ (1 - theta P x))) := Finset.sum_le_sum hkey
    _ = (M0 P / (P.q ^ P.ell * P.vmin ^ P.ell)) * (∑ w ∈ (Finset.Icc 1 N).filter
        (fun w => w.primeFactors ⊆ G.primes g),
        1 / ((w : ℝ) ^ (1 - theta P x))) := by rw [Finset.mul_sum]
    _ ≤ (M0 P / (P.q ^ P.ell * P.vmin ^ P.ell))
        * Real.exp (2 * Real.exp 1 * P.vmax) :=
        mul_le_mul_of_nonneg_left (harm_sum_le hx hG) hC1_nonneg
    _ = K0 P := by unfold K0; ring

/-- Main task, proved from per-group bounds via product over groups. -/
theorem TiltedGroupMassTask_proof : TiltedGroupMassTask := by
  classical
  unfold TiltedGroupMassTask
  intro P
  refine ⟨Cmass P, ?_⟩
  apply Filter.Eventually.mono (Filter.eventually_ge_atTop (Real.exp (thresh P)))
  intro x hx G hG N
  show (∑ v ∈ Finset.Icc 1 N, if groupFreePart G v = 1 then
      markWeight G P.q (fun _ => P.ell) v / (v : ℝ) ^ (1 - theta P x) else 0)
    ≤ L x ^ Cmass P
  rw [← Finset.sum_filter]
  set S0 := (Finset.Icc 1 N).filter (fun v => groupFreePart G v = 1) with hS0
  set U := Finset.univ.biUnion G.primes with hU
  set Sg : Fin G.size → Finset ℕ :=
    fun g => (Finset.Icc 1 N).filter (fun w => w.primeFactors ⊆ G.primes g) with hSg
  set Pg : Finset (Fin G.size → ℕ) := Fintype.piFinset Sg with hPg
  set ψ : ℕ → (Fin G.size → ℕ) :=
    fun v g => ∏ p ∈ G.primes g, p ^ v.factorization p with hψ
  haveI := Classical.decEq (Fin G.size → ℕ)
  have hq : 0 < P.q := geom_q_pos P
  -- Free part characterization.
  have hfree : ∀ v : ℕ, groupFreePart G v = 1 ↔ v.primeFactors ⊆ U := by
    intro v
    unfold groupFreePart
    rw [← hU]
    constructor
    · intro h1 p hp
      by_contra hcon
      have hmem : p ∈ v.primeFactors \ U := Finset.mem_sdiff.mpr ⟨hp, hcon⟩
      have hdvd : p ^ v.factorization p
          ∣ ∏ q ∈ v.primeFactors \ U, q ^ v.factorization q :=
        Finset.dvd_prod_of_mem _ hmem
      have hpmem := Nat.mem_primeFactors.mp hp
      have hprime : p.Prime := hpmem.1
      have hpdvd : p ∣ v := hpmem.2.1
      have hvne0 : v ≠ 0 := hpmem.2.2
      have he : v.factorization p ≠ 0 := by
        intro h0
        have hdis := (Nat.factorization_eq_zero_iff v p).mp h0
        rcases hdis with h1' | h2' | h3'
        · exact h1' hprime
        · exact h2' hpdvd
        · exact hvne0 h3'
      have hge : 2 ≤ p ^ v.factorization p := by
        have hp1 : 1 ≤ p := by
          have h2 := hprime.two_le
          omega
        exact le_trans hprime.two_le (le_self_pow₀ hp1 he)
      have hpos : 0 < ∏ q ∈ v.primeFactors \ U, q ^ v.factorization q := by
        apply Finset.prod_pos
        intro q hqmem
        have hqp : q.Prime :=
          (Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hqmem).1).1
        exact pow_pos hqp.pos _
      have hle : 2 ≤ ∏ q ∈ v.primeFactors \ U, q ^ v.factorization q :=
        le_trans hge (Nat.le_of_dvd hpos hdvd)
      omega
    · intro hsub
      have hempty : v.primeFactors \ U = ∅ :=
        Finset.sdiff_eq_empty_iff_subset.mpr hsub
      rw [hempty, Finset.prod_empty]
  have hmem0 : ∀ v ∈ S0, 1 ≤ v ∧ v ≤ N ∧ v.primeFactors ⊆ U := by
    intro v hv
    have hmem := Finset.mem_filter.mp (hS0 ▸ hv)
    have hw1 : 1 ≤ v := (Finset.mem_Icc.mp hmem.1).1
    have hwN : v ≤ N := (Finset.mem_Icc.mp hmem.1).2
    exact ⟨hw1, hwN, (hfree v).mp hmem.2⟩
  -- Splitting `v = ∏_g ψ v g`.
  have hsplit_all : ∀ v ∈ S0, v = ∏ g, ψ v g := by
    intro v hv
    obtain ⟨hv1, hvN, hvU⟩ := hmem0 v hv
    have hv := w_eq_prod_primes hv1 hvU
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin G.size))) G.primes := by
      intro g _ h _ hne
      exact G.disjoint g h hne
    have hbi : (∏ x ∈ Finset.univ.biUnion G.primes, x ^ v.factorization x)
        = ∏ x ∈ Finset.univ, ∏ i ∈ G.primes x, i ^ v.factorization i :=
      Finset.prod_biUnion hdisj
    rw [hU] at hv
    rw [hbi] at hv
    have eψ : (∏ g, ψ v g)
        = ∏ g ∈ Finset.univ, ∏ p ∈ G.primes g, p ^ v.factorization p :=
      Finset.prod_congr rfl (fun g _ => by rw [hψ])
    rw [eψ]
    exact hv
  have hpdvd_all : ∀ v ∈ S0, ∀ g, ψ v g ∣ v := by
    intro v hv g
    conv_rhs => rw [hsplit_all v hv]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
  have h1_all : ∀ v ∈ S0, ∀ g, 1 ≤ ψ v g := by
    intro v hv g
    have eψ : ψ v g = ∏ p ∈ G.primes g, p ^ v.factorization p := by rw [hψ]
    rw [eψ]
    show (0 : ℕ) < ∏ p ∈ G.primes g, p ^ v.factorization p
    apply Finset.prod_pos
    intro p hp
    have hprime : p.Prime := G.prime g p hp
    exact pow_pos hprime.pos _
  have hsub_all : ∀ v ∈ S0, ∀ g, (ψ v g).primeFactors ⊆ G.primes g := by
    intro v hv g q hq
    have hqmem := Nat.mem_primeFactors.mp hq
    have hqprime : q.Prime := hqmem.1
    have hqdvd : q ∣ ψ v g := hqmem.2.1
    have eψ : ψ v g = ∏ p ∈ G.primes g, p ^ v.factorization p := by rw [hψ]
    rw [eψ] at hqdvd
    have hqP : Prime q := hqprime.prime
    rw [hqP.dvd_finsetProd_iff _] at hqdvd
    obtain ⟨p, hpmem, hpdvdqp⟩ := hqdvd
    have hpdvd' : q ∣ p := hqprime.dvd_of_dvd_pow hpdvdqp
    have hprime : p.Prime := G.prime g p hpmem
    have heq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hprime).mp hpdvd'
    rw [heq]; exact hpmem
  have hmemG_all : ∀ v ∈ S0, ∀ g, ψ v g ∈ Sg g := by
    intro v hv g
    obtain ⟨hv1, hvN, _⟩ := hmem0 v hv
    have h1g := h1_all v hv g
    have hNg : ψ v g ≤ N :=
      le_trans (Nat.le_of_dvd (by omega) (hpdvd_all v hv g)) hvN
    have hmem : ψ v g ∈ (Finset.Icc 1 N).filter
        (fun w => w.primeFactors ⊆ G.primes g) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1g, hNg⟩, hsub_all v hv g⟩
    exact hmem
  -- `omegaGroup` agrees on `v` and its parts.
  have homega_all : ∀ v ∈ S0, ∀ g,
      omegaGroup G g v = omegaGroup G g (ψ v g) := by
    intro v hv g
    unfold omegaGroup
    have hfe : (G.primes g).filter (· ∣ v)
        = (G.primes g).filter (· ∣ ψ v g) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hpmem, hpdvd⟩
        refine ⟨hpmem, ?_⟩
        have hprime : p.Prime := G.prime g p hpmem
        have hP : Prime p := hprime.prime
        rw [hsplit_all v hv] at hpdvd
        rw [hP.dvd_finsetProd_iff _] at hpdvd
        obtain ⟨h, _, hdh⟩ := hpdvd
        by_cases heq : h = g
        · rw [← heq]; exact hdh
        · have h1h := h1_all v hv h
          have hne : ψ v h ≠ 0 := by omega
          have hpmem' : p ∈ (ψ v h).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hprime, hdh, hne⟩
          have hinh : p ∈ G.primes h := (hsub_all v hv h) hpmem'
          have hdis := G.disjoint g h (fun e => heq e.symm)
          exact absurd hinh (Finset.disjoint_left.mp hdis hpmem)
      · rintro ⟨hpmem, hpdvd⟩
        exact ⟨hpmem, Dvd.dvd.trans hpdvd (hpdvd_all v hv g)⟩
    exact congrArg Finset.card hfe
  -- `markWeight` splits as a product of `pgF`s.
  have hmark_all : ∀ v ∈ S0,
      markWeight G P.q (fun _ => P.ell) v / (v : ℝ) ^ (1 - theta P x)
      = ∏ g, pgF P x G g (ψ v g) := by
    intro v hv
    obtain ⟨hv1, hvN, hvU⟩ := hmem0 v hv
    have e1 : ∀ g : Fin G.size,
        ((Nat.descFactorial (omegaGroup G g (ψ v g)) P.ell : ℝ)
          * P.q ^ (((omegaGroup G g (ψ v g) : ℤ)) - (P.ell : ℤ))
          / mass G g ^ P.ell)
        = (((Nat.descFactorial (omegaGroup G g v) P.ell : ℝ)) / mass G g ^ P.ell)
          * P.q ^ ((((omegaGroup G g v : ℤ)) - (P.ell : ℤ))) := by
      intro g
      rw [← homega_all v hv g]
      ring
    have e2 : (∏ g, ((Nat.descFactorial (omegaGroup G g (ψ v g)) P.ell : ℝ)
          * P.q ^ (((omegaGroup G g (ψ v g) : ℤ)) - (P.ell : ℤ))
          / mass G g ^ P.ell))
        = (∏ g, ((Nat.descFactorial (omegaGroup G g v) P.ell : ℝ))
          / mass G g ^ P.ell)
          * (∏ g, P.q ^ ((((omegaGroup G g v : ℤ)) - (P.ell : ℤ)))) :=
      calc (∏ g, ((Nat.descFactorial (omegaGroup G g (ψ v g)) P.ell : ℝ)
            * P.q ^ (((omegaGroup G g (ψ v g) : ℤ)) - (P.ell : ℤ))
            / mass G g ^ P.ell))
          = ∏ g, (((Nat.descFactorial (omegaGroup G g v) P.ell : ℝ))
            / mass G g ^ P.ell
            * P.q ^ ((((omegaGroup G g v : ℤ)) - (P.ell : ℤ)))) :=
            Finset.prod_congr rfl (fun g _ => e1 g)
        _ = (∏ g, ((Nat.descFactorial (omegaGroup G g v) P.ell : ℝ))
            / mass G g ^ P.ell)
            * (∏ g, P.q ^ ((((omegaGroup G g v : ℤ)) - (P.ell : ℤ)))) :=
            Finset.prod_mul_distrib
    have hexp : (∑ g : Fin G.size,
          ((omegaGroup G g v : ℤ) - (P.ell : ℤ)))
        = ((omega G v : ℤ) - ∑ g : Fin G.size, (((fun _ => P.ell) g : ℤ))) := by
      unfold omega
      rw [Nat.cast_sum, Finset.sum_sub_distrib]
    have hQ : P.q ^ ((omega G v : ℤ) - ∑ g : Fin G.size, (((fun _ => P.ell) g : ℤ)))
        = ∏ g, P.q ^ ((((omegaGroup G g v : ℤ)) - (P.ell : ℤ))) := by
      rw [← zpow_sum_eq (Finset.univ : Finset (Fin G.size))
        (fun g => ((omegaGroup G g v : ℤ) - (P.ell : ℤ))) (ne_of_gt hq)]
      congr 1
      exact hexp.symm
    have e3 : (∏ g, ((ψ v g : ℝ)) ^ (1 - theta P x))
        = (v : ℝ) ^ (1 - theta P x) := by
      have hnn : ∀ g ∈ (Finset.univ : Finset (Fin G.size)),
          (0 : ℝ) ≤ (((ψ v g : ℕ)) : ℝ) :=
        fun g _ => Nat.cast_nonneg _
      have e := rpow_prod_eq Finset.univ
        (fun g => (((ψ v g : ℕ)) : ℝ)) (1 - theta P x) hnn
      rw [← e]
      congr 1
      have hc := (congrArg (fun n : ℕ => ((n : ℝ))) (hsplit_all v hv)).symm
      rw [Nat.cast_prod] at hc
      exact hc
    have r1 : (∏ g, pgF P x G g (ψ v g))
        = (∏ g, ((Nat.descFactorial (omegaGroup G g (ψ v g)) P.ell : ℝ)
          * P.q ^ (((omegaGroup G g (ψ v g) : ℤ)) - (P.ell : ℤ))
          / mass G g ^ P.ell))
          / (∏ g, ((ψ v g : ℝ)) ^ (1 - theta P x)) := by
      unfold pgF
      exact Finset.prod_div_distrib _ _
    have hmw : markWeight G P.q (fun _ => P.ell) v
        = (P.q ^ ((omega G v : ℤ) - ∑ g : Fin G.size, (((fun _ => P.ell) g : ℤ))))
          * (∏ g, ((Nat.descFactorial (omegaGroup G g v) P.ell : ℝ))
            / mass G g ^ P.ell) := rfl
    rw [r1, e2, ← hQ, e3, hmw]
    ring
  -- Injection into the pi-product.
  have hinjG : Set.InjOn ψ (↑S0) := by
    intro a ha b hb hab
    have ha0 := Finset.mem_coe.mp ha
    have hb0 := Finset.mem_coe.mp hb
    have ha_eq := hsplit_all a ha0
    have hb_eq := hsplit_all b hb0
    have hparts : (∏ g, ψ a g) = ∏ g, ψ b g :=
      congrArg (fun f => ∏ g, f g) hab
    exact ha_eq.trans (hparts.trans hb_eq.symm)
  have hsumG : (∑ v ∈ S0, markWeight G P.q (fun _ => P.ell) v
        / (v : ℝ) ^ (1 - theta P x))
      = ∑ y ∈ S0.image ψ, ∏ g, pgF P x G g (y g) := by
    rw [Finset.sum_image hinjG]
    exact Finset.sum_congr rfl (fun v hv => hmark_all v hv)
  have hsubG_img : S0.image ψ ⊆ Pg := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact Fintype.mem_piFinset.mpr (hmemG_all v hv)
  have hnnG2 : ∀ y ∈ Pg, y ∉ S0.image ψ →
      0 ≤ ∏ g, pgF P x G g (y g) := by
    intro y _ _
    exact Finset.prod_nonneg (fun g _ => pgF_nonneg P x G g (y g))
  have hleG : (∑ y ∈ S0.image ψ, ∏ g, pgF P x G g (y g))
      ≤ ∑ y ∈ Pg, ∏ g, pgF P x G g (y g) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubG_img hnnG2
  have hpiG : (∑ y ∈ Pg, ∏ g, pgF P x G g (y g))
      = ∏ g, ∑ w ∈ Sg g, pgF P x G g w :=
    (Finset.prod_univ_sum _ _).symm
  have hfinG1 : (∏ g, ∑ w ∈ Sg g, pgF P x G g w) ≤ ∏ g, K0 P :=
    Finset.prod_le_prod₀
      (fun g _ => Finset.sum_nonneg (fun w _ => pgF_nonneg P x G g w))
      (fun g _ => per_group_le hx hG)
  have hfinG2 : (∏ _g : Fin G.size, K0 P) = (K0 P) ^ G.size := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Size bound and `K0^size ≤ L^C`.
  have hcard : G.small.card + G.big.card = G.size := by
    have hbig : G.big = Finset.univ \ G.small := rfl
    have h1 : G.small.card + (Finset.univ \ G.small).card
        = (Finset.univ : Finset (Fin G.size)).card := by
      rw [Finset.card_sdiff, Finset.inter_univ]
      exact Nat.add_sub_cancel' (Finset.card_le_univ _)
    rw [hbig, h1, Finset.card_univ, Fintype.card_fin]
  have hsize : (G.size : ℝ) ≤ 2 * P.C₀ * T x := by
    have hs : ((G.small.card : ℕ) : ℝ) ≤ P.C₀ * T x := hG.1.2
    have hb : ((G.big.card : ℕ) : ℝ) ≤ P.C₀ * T x := hG.2.1.2
    have hc : (G.size : ℝ) = ((G.small.card : ℕ) : ℝ) + ((G.big.card : ℕ) : ℝ) := by
      exact_mod_cast hcard.symm
    rw [hc]
    linarith
  have hKL : (K0 P) ^ G.size ≤ L x ^ Cmass P := by
    have hK0 : 0 < K0 P := K0_pos P
    have hL1 : 1 < L x := L_gt_one_of_ge hx
    have hLpos : 0 < L x := L_pos_of_ge hx
    have e1 : (K0 P) ^ G.size = Real.exp ((G.size : ℝ) * Real.log (K0 P)) := by
      conv_lhs => rw [← Real.exp_log hK0, ← Real.exp_nat_mul]
    have e2 : L x ^ Cmass P = Real.exp (Real.log (L x) * Cmass P) :=
      Real.rpow_def_of_pos hLpos _
    rw [e1, e2]
    apply Real.exp_le_exp.mpr
    have hT : T x = Real.log (L x) := rfl
    have hlogL : 0 < Real.log (L x) := Real.log_pos hL1
    have hC0 : 0 < P.C₀ := geom_C0_pos P
    by_cases hK : Real.log (K0 P) ≤ 0
    · have h1 : (G.size : ℝ) * Real.log (K0 P) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hK
      have h2 : 0 ≤ Real.log (L x) * Cmass P :=
        mul_nonneg (le_of_lt hlogL) (Cmass_nonneg P)
      linarith
    · push_neg at hK
      have hnn : (0 : ℝ) ≤ 2 * P.C₀ * Real.log (K0 P) :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC0)) (le_of_lt hK)
      have hmax : Cmass P = 2 * P.C₀ * Real.log (K0 P) := by
        unfold Cmass
        exact max_eq_right hnn
      rw [hmax]
      have hsize2 : (G.size : ℝ) ≤ 2 * P.C₀ * Real.log (L x) := by
        rw [← hT]; exact hsize
      calc (G.size : ℝ) * Real.log (K0 P)
          ≤ (2 * P.C₀ * Real.log (L x)) * Real.log (K0 P) :=
            mul_le_mul_of_nonneg_right hsize2 (le_of_lt hK)
        _ = Real.log (L x) * (2 * P.C₀ * Real.log (K0 P)) := by ring
  calc (∑ v ∈ S0, markWeight G P.q (fun _ => P.ell) v / (v : ℝ) ^ (1 - theta P x))
      = ∑ y ∈ S0.image ψ, ∏ g, pgF P x G g (y g) := hsumG
    _ ≤ ∑ y ∈ Pg, ∏ g, pgF P x G g (y g) := hleG
    _ = ∏ g, ∑ w ∈ Sg g, pgF P x G g w := hpiG
    _ ≤ ∏ _g : Fin G.size, K0 P := hfinG1
    _ = (K0 P) ^ G.size := hfinG2
    _ ≤ L x ^ Cmass P := hKL

end Erdos821.P6Mass
