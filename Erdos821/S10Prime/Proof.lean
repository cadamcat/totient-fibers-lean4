import Erdos821.S10Prime.Basic

/-! Two Type II prime-to-proxy replacements in the balanced window (paper §6,
balanced composites). The first prime indicator is replaced using Type II with
the proxy discrepancy; the second is replaced by Type II with the factor roles
exchanged, the remaining coefficient being a proxy bounded by one. The product
of the two proxies is bounded by the uniform density constant of
`ProxyDensities`, which is fixed before κ. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace Erdos821.S10Prime
open Erdos821.Blueprint Erdos821.P10 Erdos821.P7Core
attribute [local instance] Classical.propDecidable

theorem proxyConstant_prime_nonneg (x S : ℝ) (m : ℕ) :
    0 ≤ proxyConstant .prime x S m := by
  unfold proxyConstant
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro n _
    by_cases hn : n.Prime <;> simp [test, hn]
  · exact Nat.cast_nonneg _

/-- One dyadic box of a prime-minus-proxy error term, at a fixed large `x`. -/
theorem error_box_bound (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (κ S B Kt Dsave bstar lo hi : ℝ)
    (hx : 1 ≤ x) (hL : 1 ≤ Analytic.L x) (hKt : 0 < Kt)
    (hSupport : ∀ u : ℕ, C.weighted x jstar u ≠ 0 → x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x)
    (hlohi : lo ≤ hi) (hlo : 2 * x ^ bstar ≤ lo) (hhi : hi ≤ x ^ (1 - bstar))
    (hlo4 : x ^ ((1 : ℝ) / 4) ≤ lo) (hhi4 : hi ≤ x ^ (1 - (1 : ℝ) / 4))
    (hW : Analytic.W x < lo)
    (hTypeII : ∀ (U V : ℝ) (a b : ℕ → ℂ),
      x / 8 ≤ U * V → U * V ≤ 8 * x →
      x ^ bstar ≤ U → U ≤ x ^ (1 - bstar) →
      x ^ bstar ≤ V → V ≤ x ^ (1 - bstar) →
      (∀ n, ‖a n‖ ≤ Analytic.L x ^ (1 : ℝ) ∧ ‖b n‖ ≤ Analytic.L x ^ (1 : ℝ)) →
      (∀ n, a n ≠ 0 → Analytic.rough (Analytic.W x) n) →
      Analytic.discrepancy x B (restricted U a) →
      ‖typeIISum C.bands x jstar U V C.psi a b‖ ≤ Kt * x * Analytic.L x ^ (-Dsave))
    (hProxy : ∀ (I : FactorTest) (lo hi : ℝ), TestAllowed 1 κ I →
      x ^ ((1 : ℝ) / 4) ≤ lo → lo ≤ hi → hi ≤ x ^ (1 - (1 : ℝ) / 4) →
      Analytic.discrepancy x B (proxyDifference I x S lo hi) ∧
      (∀ n : ℕ, lo ≤ (n : ℝ) → (n : ℝ) ≤ hi →
        0 < proxyDenominator x S n ∧ 0 ≤ proxy I x S n ∧ proxy I x S n ≤ 1))
    (b : ℕ → ℝ) (hb1 : ∀ n, |b n| ≤ 1)
    (hbsupp : ∀ n, b n ≠ 0 → lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi) (U V : ℕ) :
    |pairBox C x jstar (cut lo hi (fun n => test .prime x n - proxy .prime x S n)) b U V| ≤
      Kt * x * Analytic.L x ^ (-Dsave) := by
  set d := cut lo hi (fun n => test .prime x n - proxy .prime x S n) with hd
  have hE0 : 0 ≤ Kt * x * Analytic.L x ^ (-Dsave) :=
    mul_nonneg (mul_nonneg hKt.le (by linarith)) (Real.rpow_nonneg (by linarith) _)
  by_cases hz : pairBox C x jstar d b U V = 0
  · rw [hz, abs_zero]
    exact hE0
  obtain ⟨m, hm, n, hn, hk, ha, hb⟩ := pairBox_ne_zero hz
  have hmw := cut_ne_zero ha
  have hnw := hbsupp n hb
  obtain ⟨u, hprod, hwu⟩ := pairKernel_ne_zero hk
  have hsu := hSupport u hwu
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    box_ranges x bstar lo hi m n u U V hx hlo hhi hmw hnw hm hn hprod hsu
  have hPw := (hProxy .prime lo hi trivial hlo4 hlohi hhi4).2
  have hd1 : ∀ k, |d k| ≤ 1 := by
    intro k
    simp only [hd, cut]
    split_ifs with hk'
    · obtain ⟨_, hp0, hp1⟩ := hPw k hk'.1 hk'.2
      have ht : 0 ≤ test .prime x k ∧ test .prime x k ≤ 1 := by
        by_cases hpk : k.Prime <;> simp [test, hpk]
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    · simp
  have hdrough : ∀ k, ((d k : ℝ) : ℂ) ≠ 0 → Analytic.rough (Analytic.W x) k := by
    intro k hk'
    have hk'' : d k ≠ 0 := by exact_mod_cast hk'
    have hkw := cut_ne_zero hk''
    simp only [hd, cut, if_pos hkw] at hk''
    by_cases hpk : k.Prime
    · refine ⟨hpk.pos, ?_⟩
      intro q hq hqk
      have hqk' : q = k := (Nat.prime_dvd_prime_iff_eq hq hpk).1 hqk
      rw [hqk']
      linarith [hkw.1]
    · have htest : test .prime x k = 0 := by simp [test, hpk]
      rw [htest] at hk''
      unfold proxy at hk''
      by_contra hr
      rw [if_neg hr] at hk''
      exact hk'' (by ring)
  rcases Finset.mem_Ico.mp hm with ⟨hUm, hm2U⟩
  have hU1 : 1 ≤ U := by omega
  set lo' := max (U : ℝ) lo with hlo'
  set hi' := min ((2 * U - 1 : ℕ) : ℝ) hi with hhi'
  have hcastlt : ∀ k : ℕ, (k : ℝ) < 2 * (U : ℝ) ↔ (k : ℝ) ≤ ((2 * U - 1 : ℕ) : ℝ) := by
    intro k
    constructor
    · intro hlt
      have : k < 2 * U := by exact_mod_cast hlt
      have : k ≤ 2 * U - 1 := by omega
      exact_mod_cast this
    · intro hle
      have : k ≤ 2 * U - 1 := by exact_mod_cast hle
      have : k < 2 * U := by omega
      exact_mod_cast this
  have hrestr : restricted (U : ℝ) (fun k => ((d k : ℝ) : ℂ)) =
      proxyDifference .prime x S lo' hi' := by
    funext k
    simp only [restricted, proxyDifference, hd, cut]
    by_cases hc : lo' ≤ (k : ℝ) ∧ (k : ℝ) ≤ hi'
    · have hc1 := max_le_iff.mp hc.1
      have hc2 := le_min_iff.mp hc.2
      have hk1 : (U : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) < 2 * (U : ℝ) :=
        ⟨hc1.1, (hcastlt k).2 hc2.1⟩
      have hk2 : lo ≤ (k : ℝ) ∧ (k : ℝ) ≤ hi := ⟨hc1.2, hc2.2⟩
      rw [if_pos hk1, if_pos hk2, if_pos hc]
    · rw [if_neg hc]
      by_cases hk1 : (U : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) < 2 * (U : ℝ)
      · have hk2 : ¬ (lo ≤ (k : ℝ) ∧ (k : ℝ) ≤ hi) := by
          intro hk2
          exact hc ⟨max_le hk1.1 hk2.1, le_min ((hcastlt k).1 hk1.2) hk2.2⟩
        rw [if_pos hk1, if_neg hk2]
        simp
      · rw [if_neg hk1]
  have hmle : (m : ℝ) ≤ ((2 * U - 1 : ℕ) : ℝ) :=
    (hcastlt m).1 (by exact_mod_cast hm2U)
  have hlo'hi' : lo' ≤ hi' :=
    le_trans (max_le (by exact_mod_cast hUm) hmw.1) (le_min hmle hmw.2)
  have hdisc := (hProxy .prime lo' hi' trivial (le_trans hlo4 (le_max_right _ _))
    hlo'hi' (le_trans (min_le_right _ _) hhi4)).1
  have hcoeff : ∀ k, ‖((d k : ℝ) : ℂ)‖ ≤ Analytic.L x ^ (1 : ℝ) ∧
      ‖((b k : ℝ) : ℂ)‖ ≤ Analytic.L x ^ (1 : ℝ) := by
    intro k
    rw [Real.rpow_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact ⟨(hd1 k).trans hL, (hb1 k).trans hL⟩
  have hT := hTypeII (U : ℝ) (V : ℝ) (fun k => ((d k : ℝ) : ℂ)) (fun k => ((b k : ℝ) : ℂ))
    h1 h2 h3 h4 h5 h6 hcoeff hdrough (by rw [hrestr]; exact hdisc)
  rw [typeIISum_eq_pairBox, Complex.norm_real, Real.norm_eq_abs] at hT
  exact hT

/-- Summing the box bound over the `K²` natural dyadic boxes. -/
theorem fullPair_abs_le_boxes (C : CandidateData) (x : ℝ) (jstar K : ℕ)
    (a b : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hbox : ∀ U V : ℕ, |pairBox C x jstar a b U V| ≤ E) :
    |fullPair C x jstar K a b| ≤ (K : ℝ) * ((K : ℝ) * E) := by
  rw [fullPair_eq_boxes]
  have h := abs_sum_le_card_mul_bound (Finset.range K)
    (fun k => ∑ l ∈ Finset.range K, pairBox C x jstar a b (2 ^ k) (2 ^ l))
    ((K : ℝ) * E) (mul_nonneg (Nat.cast_nonneg _) hE) (by
      intro k _
      have h' := abs_sum_le_card_mul_bound (Finset.range K)
        (fun l => pairBox C x jstar a b (2 ^ k) (2 ^ l)) E hE
        (fun l _ => hbox _ _)
      simpa using h')
  simpa using h

/-- Absorb the `2K²` Type II boxes into `ε·mass/L`. -/
theorem absorb_boxes (K : ℕ) (L x Kt CA Dsave ε mass : ℝ) (hL1 : 1 ≤ L) (hx : 0 < x)
    (hKt : 0 < Kt) (hε : 0 < ε) (hLbig : 72 * Kt / ε ≤ L)
    (hKL : (K : ℝ) ≤ (3 / Real.log 2) * L + 1) (hD : CA + 4 ≤ Dsave)
    (hmass : x * L ^ (-CA) ≤ mass) :
    (K : ℝ) * ((K : ℝ) * (Kt * x * L ^ (-Dsave))) +
        (K : ℝ) * ((K : ℝ) * (Kt * x * L ^ (-Dsave))) ≤ ε * mass / L := by
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := hLpos.ne'
  have hlog2 : (3 : ℝ) / Real.log 2 ≤ 5 := by
    rw [div_le_iff₀ (Real.log_pos one_lt_two)]
    linarith [Real.log_two_gt_d9]
  have hK6 : (K : ℝ) ≤ 6 * L := by
    have := mul_le_mul_of_nonneg_right hlog2 hLpos.le
    linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  set E := Kt * x * L ^ (-Dsave) with hE
  have hE0 : 0 ≤ E := mul_nonneg (mul_nonneg hKt.le hx.le) (Real.rpow_nonneg hLpos.le _)
  have hKK : (K : ℝ) * (K : ℝ) ≤ 36 * L ^ 2 := by
    have := mul_le_mul hK6 hK6 hK0 (by linarith)
    nlinarith
  have step1 : (K : ℝ) * ((K : ℝ) * E) + (K : ℝ) * ((K : ℝ) * E) ≤ 72 * (L ^ 2 * E) := by
    have := mul_le_mul_of_nonneg_right hKK hE0
    nlinarith
  have hrp : L ^ (-Dsave) ≤ L ^ (-CA) * (L ^ (4 : ℕ))⁻¹ := by
    have h4 : L ^ (-CA - 4) = L ^ (-CA) * (L ^ (4 : ℕ))⁻¹ := by
      rw [Real.rpow_sub hLpos, div_eq_mul_inv,
        show L ^ (4 : ℝ) = L ^ (4 : ℕ) by exact_mod_cast Real.rpow_natCast L 4]
    rw [← h4]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hA0 : 0 ≤ x * L ^ (-CA) := mul_nonneg hx.le (Real.rpow_nonneg hLpos.le _)
  have step2 : L ^ 2 * E ≤ Kt * mass / L ^ 2 := by
    have h1 : L ^ 2 * E ≤ L ^ 2 * (Kt * x * (L ^ (-CA) * (L ^ (4 : ℕ))⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hrp (mul_nonneg hKt.le hx.le)
    have h2 : L ^ 2 * (Kt * x * (L ^ (-CA) * (L ^ (4 : ℕ))⁻¹)) =
        Kt * (x * L ^ (-CA)) / L ^ 2 := by
      have hL2 : L ^ 2 * (L ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hLne)
      have hL4 : (L ^ (4 : ℕ))⁻¹ = (L ^ 2)⁻¹ * (L ^ 2)⁻¹ := by rw [← mul_inv, ← pow_add]
      rw [hL4, div_eq_mul_inv]
      linear_combination (Kt * x * L ^ (-CA) * (L ^ 2)⁻¹) * hL2
    have h3 : Kt * (x * L ^ (-CA)) / L ^ 2 ≤ Kt * mass / L ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hmass hKt.le
    linarith
  have hmass0 : 0 ≤ mass := le_trans hA0 hmass
  have step3 : 72 * (Kt * mass / L ^ 2) ≤ ε * mass / L := by
    have hKtL : 72 * Kt ≤ ε * L := by
      rw [div_le_iff₀ hε] at hLbig
      linarith
    have : 72 * (Kt * mass / L ^ 2) = (72 * Kt) * mass / L / L := by
      ring
    rw [this]
    have h' : (72 * Kt) * mass / L ≤ (ε * L) * mass / L := by
      apply div_le_div_of_nonneg_right _ hLpos.le
      exact mul_le_mul_of_nonneg_right hKtL hmass0
    have h'' : (ε * L) * mass / L = ε * mass := by
      rw [mul_comm ε L, mul_assoc, mul_div_cancel_left₀ _ hLne]
    calc (72 * Kt) * mass / L / L ≤ (ε * L) * mass / L / L :=
          div_le_div_of_nonneg_right h' hLpos.le
      _ = ε * mass / L := by rw [h'']
  linarith

theorem BalancedWindowPrimeTask_proof : BalancedWindowPrimeTask := by
  intro hc hII hp δ C hGeom hBounds
  obtain ⟨Kd, hKd, hdens⟩ := hp.densities.1
  refine ⟨Kd ^ 2, by positivity, ?_⟩
  intro κ bstar hκ hκ' hbstar hbstar' jstar hj hslot ε hε
  obtain ⟨hValid, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPsi, hSupp, -, -⟩ :=
    hGeom
  obtain ⟨Kc, CA, cmin, cmax, -, -, -, hB⟩ := hBounds
  set Dsave : ℝ := max CA 0 + 4 with hDsave
  have hDsave0 : 0 < Dsave := by have := le_max_right CA 0; linarith
  have hDCA : CA + 4 ≤ Dsave := by have := le_max_left CA 0; linarith
  obtain ⟨B, Kt, hB0, hKt, hTII⟩ :=
    hII C.bands hValid Dsave bstar 1 hDsave0 hbstar one_pos jstar hslot C.psi hPsi hSupp
  set S : ℝ := 2 * B + 4 with hS
  have hPD := hp.discrepancy 1 κ B one_pos hκ hκ' hB0 S (by linarith)
  have hD := hdens κ S hκ hκ' (by linarith)
  have hLev : ∀ᶠ x : ℝ in atTop, max 1 (72 * Kt / ε) ≤ Analytic.L x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hWev := eventually_W_le_rpow (1 / 4 : ℝ) (by norm_num)
  have hgap : 0 < 1 / 2 - 2 * κ - bstar := by linarith
  have hSlack : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (1 / 2 - 2 * κ - bstar) :=
    (tendsto_rpow_atTop hgap).eventually_ge_atTop 2
  filter_upwards [hTII, hPD, hD, hB jstar hj, eventually_ge_atTop (3 : ℝ), hLev, hWev,
    hSlack] with x hTx hPx hDx hBx hx3 hLx hWx hSlx
  obtain ⟨hmass, -, -, hw0, -, hsupp⟩ := hBx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hL1 : 1 ≤ Analytic.L x := le_trans (le_max_left _ _) hLx
  set lo := x ^ (1 / 2 - 2 * κ) with hlo_def
  set hi := x ^ (1 / 2 + 2 * κ) with hhi_def
  have hlo1 : 1 ≤ lo := Real.one_le_rpow hx1 (by linarith)
  have hlohi : lo ≤ hi := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hlo2 : 2 * x ^ bstar ≤ lo := by
    have hsplit : lo = x ^ bstar * x ^ (1 / 2 - 2 * κ - bstar) := by
      rw [hlo_def, ← Real.rpow_add hxpos]
      congr 1
      ring
    rw [hsplit]
    have := Real.rpow_nonneg hxpos.le bstar
    nlinarith
  have hhi1 : hi ≤ x ^ (1 - bstar) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hlo4 : x ^ ((1 : ℝ) / 4) ≤ lo := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hhi4 : hi ≤ x ^ (1 - (1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hWlo : Analytic.W x < lo :=
    lt_of_le_of_lt hWx (Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith))
  obtain ⟨K, hK5, hKL⟩ := exists_logarithmic_dyadic_cutoff x hx3
  have hhix : hi ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show 1 / 2 + 2 * κ ≤ (1 : ℝ) by linarith)
    rwa [Real.rpow_one] at h
  have hhiK : hi < ((2 ^ K : ℕ) : ℝ) := by linarith
  have hhi0 : 0 ≤ hi := by linarith
  set P := cut lo hi (test .prime x) with hP
  set p := cut lo hi (proxy .prime x S) with hp_def
  set d := cut lo hi (fun n => test .prime x n - proxy .prime x S n) with hd
  set R := cut lo hi (fun m => if Analytic.rough (Analytic.W x) m then (1 : ℝ) else 0) with hR
  have hprime : balancedPrimeWindowMass C x jstar κ = fullPair C x jstar K P P :=
    balancedPairWindowMass_eq_fullPair C x jstar κ _ _ K hlo1 hhi0 hhiK
  have hrough : balancedRoughWindowMass C x jstar κ = fullPair C x jstar K R R :=
    balancedPairWindowMass_eq_fullPair C x jstar κ _ _ K hlo1 hhi0 hhiK
  have hdec := fullPair_decompose C x jstar K P p d
    (fun n => cut_sub lo hi (test .prime x) (proxy .prime x S) n)
  have hPw := (hPx .prime lo hi trivial hlo4 hlohi hhi4).2
  have hSupport : ∀ u : ℕ, C.weighted x jstar u ≠ 0 → x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x :=
    fun u hu => ⟨(hsupp u hu).1, (hsupp u hu).2.1⟩
  have hE0 : 0 ≤ Kt * x * Analytic.L x ^ (-Dsave) :=
    mul_nonneg (mul_nonneg hKt.le hxpos.le) (Real.rpow_nonneg (by linarith) _)
  have hbox := error_box_bound C x jstar κ S B Kt Dsave bstar lo hi hx1 hL1 hKt hSupport
    hlohi hlo2 hhi1 hlo4 hhi4 hWlo hTx hPx
  have hP1 : ∀ n, |P n| ≤ 1 := by
    intro n
    simp only [hP, cut]
    split_ifs
    · by_cases hpn : n.Prime <;> simp [test, hpn]
    · simp
  have hp1 : ∀ n, |p n| ≤ 1 := by
    intro n
    simp only [hp_def, cut]
    split_ifs with hn
    · obtain ⟨_, h0, h1⟩ := hPw n hn.1 hn.2
      rw [abs_le]
      constructor <;> linarith
    · simp
  have hE1 : |fullPair C x jstar K d P| ≤ (K : ℝ) * ((K : ℝ) * (Kt * x * Analytic.L x ^ (-Dsave))) :=
    fullPair_abs_le_boxes C x jstar K d P _ hE0 (hbox P hP1 (fun n h => cut_ne_zero h))
  have hE2 : |fullPair C x jstar K p d| ≤ (K : ℝ) * ((K : ℝ) * (Kt * x * Analytic.L x ^ (-Dsave))) := by
    rw [fullPair_swap]
    exact fullPair_abs_le_boxes C x jstar K d p _ hE0 (hbox p hp1 (fun n h => cut_ne_zero h))
  set c := Kd / (Analytic.L x * sieveProduct (Analytic.W x)) with hc_def
  have hmaj : ∀ n, 0 ≤ p n ∧ p n ≤ c * R n := by
    intro n
    simp only [hp_def, hR, cut]
    by_cases hw : lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi
    · simp only [if_pos hw]
      unfold proxy
      by_cases hr : Analytic.rough (Analytic.W x) n
      · simp only [if_pos hr, mul_one]
        exact ⟨proxyConstant_prime_nonneg x S n, hDx n hw.1 hw.2⟩
      · simp [hr]
    · simp [hw]
  have hM := fullPair_le_of_majorant C x jstar K hw0 p R c hmaj
  have hc2 : c ^ 2 = Kd ^ 2 / (Analytic.L x ^ 2 * sieveProduct (Analytic.W x) ^ 2) := by
    rw [hc_def, div_pow, mul_pow]
  have habs := absorb_boxes K (Analytic.L x) x Kt CA Dsave ε (C.mass x jstar) hL1 hxpos hKt hε
    (le_trans (le_max_right _ _) hLx) hKL hDCA hmass
  rw [hprime, hrough, hdec, ← hc2]
  have h1 := abs_le.mp hE1
  have h2 := abs_le.mp hE2
  linarith

end Erdos821.S10Prime

namespace Erdos821.P7Core

/-- Export of the balanced prime-replacement task in the task's namespace. -/
theorem BalancedWindowPrimeTask_proof : BalancedWindowPrimeTask :=
  Erdos821.S10Prime.BalancedWindowPrimeTask_proof

end Erdos821.P7Core
