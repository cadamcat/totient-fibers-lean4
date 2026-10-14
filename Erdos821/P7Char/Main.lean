import Erdos821.P7Char.Assembly
import Erdos821.P7Char.Asymptotics

/-! Proof of `NonprincipalTypeITask`: parameter choices and asymptotic bookkeeping. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory Erdos821.Blueprint.Analytic
open scoped Classical

namespace Erdos821.P7Char

open Erdos821.Blueprint

theorem sqrt_le_of_le_sq {y z : ℝ} (hz : 0 ≤ z) (h : y ≤ z ^ 2) : Real.sqrt y ≤ z :=
  (Real.sqrt_le_sqrt h).trans (Real.sqrt_sq hz).le

theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem rpow_div_two_sq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ (a / 2)) ^ 2 = x ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

theorem sum_le_mul_sum_div (N : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ Finset.Icc 1 N, f n ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, f n / n := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast h2
  calc f n = (n : ℝ) * (f n / n) := by field_simp
    _ ≤ (N : ℝ) * (f n / n) := mul_le_mul_of_nonneg_right hnN (div_nonneg (hf n) hn0.le)

theorem bb_le (K : ℝ) (hK : 0 ≤ K) (Q R NA NB : ℕ) (hQ : 1 ≤ Q) (βB : ℝ)
    (P1 P2 P3 P4 P5 P6 : ℝ) (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (hP3 : 0 < P3) (hP4 : 0 ≤ P4)
    (hP5 : 0 ≤ P5)
    (h1 : ((NA : ℝ) + 1) * βB ≤ P1 ^ 2) (h2 : ((NA : ℝ) + 1) * ((NB : ℝ) + 1) ≤ P2 ^ 2)
    (hR : P3 ≤ (R : ℝ) + 1) (h3 : Real.log (4 * Q) ≤ P4 ^ 2) (h4 : (NA : ℝ) + 1 ≤ P5 ^ 2)
    (h5 : (NB : ℝ) + 1 ≤ P5 ^ 2) (h6 : 2 * (Q : ℝ) * Real.log (4 * Q) ≤ P6) :
    blockBB K Q R NA NB βB ≤ 2 * K * P1 * (P2 / P3 + P4 * (P5 + P5) + P6) := by
  unfold blockBB
  have hlog0 : 0 ≤ Real.log (4 * (Q : ℝ)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith)
  have b1 := sqrt_le_of_le_sq hP1 h1
  have b2 : Real.sqrt (((NA : ℝ) + 1) * ((NB : ℝ) + 1)) / ((R : ℝ) + 1) ≤ P2 / P3 := by
    calc _ ≤ Real.sqrt (((NA : ℝ) + 1) * ((NB : ℝ) + 1)) / P3 :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hP3 hR
      _ ≤ P2 / P3 := div_le_div_of_nonneg_right (sqrt_le_of_le_sq hP2 h2) hP3.le
  have b3 := sqrt_le_of_le_sq hP4 h3
  have b4 := sqrt_le_of_le_sq hP5 h4
  have b5 := sqrt_le_of_le_sq hP5 h5
  have hs0 : 0 ≤ Real.sqrt ((NA : ℝ) + 1) + Real.sqrt ((NB : ℝ) + 1) := by positivity
  have hK2 : 0 ≤ 2 * K := mul_nonneg (by norm_num) hK
  have hfac : 0 ≤ Real.sqrt (((NA : ℝ) + 1) * ((NB : ℝ) + 1)) / ((R : ℝ) + 1) +
      Real.sqrt (Real.log (4 * Q)) * (Real.sqrt ((NA : ℝ) + 1) + Real.sqrt ((NB : ℝ) + 1)) +
      2 * Q * Real.log (4 * Q) :=
    add_nonneg (add_nonneg (div_nonneg (Real.sqrt_nonneg _) (by positivity))
      (mul_nonneg (Real.sqrt_nonneg _) hs0)) (mul_nonneg (by positivity) hlog0)
  apply mul_le_mul (mul_le_mul_of_nonneg_left b1 hK2) _ hfac (mul_nonneg hK2 hP1)
  exact add_le_add (add_le_add b2 (mul_le_mul b3 (add_le_add b4 b5) hs0 hP4)) h6

theorem twisted_zero_of_empty (C : CandidateData) (x : ℝ) (hx : 0 < x) (jstar : ℕ)
    (s₀ : C.bands.Slot x) (hψ : Function.support C.psi ⊆ Set.Icc 1 2)
    (hempty : C.bands.slotValues x jstar s₀ = ∅) (Q h : ℕ) (χ : CharacterIndex Q) :
    twisted (Finset.Icc 1 ⌊2 * x⌋₊) (C.weighted x jstar) h χ = 0 := by
  have hB : ∀ p ∈ C.bands.slotValues x jstar s₀,
      p.Prime ∧ S56Core.GroupFree (C.bands.groups x) p := by
    intro p hp
    rw [hempty] at hp
    simp at hp
  rw [twisted_eq_cv, weighted_sum_extract C x hx jstar s₀ hB hψ (cv h χ) (fun _ => 0)
    (by intro p hp; rw [hempty] at hp; simp at hp), hempty, Finset.sum_empty]

set_option maxHeartbeats 4000000 in
theorem main_bound (hc : ClassicalInputs) (δ : ℝ) (C : CandidateData) (hC : C.Geometry δ)
    (θ D : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hD : 0 < D) (jstar : ℕ) (hj : C.j₀ ≤ jstar) :
    ∀ᶠ x : ℝ in atTop, (∑ d ∈ oddSqfreeModuli (x ^ θ),
        |progressionSum C x jstar d -
          Erdos821.P7B.coprimeMass C x jstar d / (Nat.totient d : ℝ)|) ≤
      5 * (x * L x ^ (-D)) := by
  obtain ⟨Mψ, hMψ0, hMψ⟩ := Erdos821.P7B.candidate_psi_bounds C δ hC
  have hMψabs : ∀ y, |C.psi y| ≤ Mψ := fun y => by
    rw [abs_of_nonneg (hMψ y).1]; exact (hMψ y).2
  obtain ⟨hV, _, _, _, _, _, _, hpre, _, _, _, _, _, _, _, _, _, _, _, _, hψs, hψsupp, _, _⟩ :=
    hC
  have hjpos : 0 < jstar := by omega
  have hV' := hV
  obtain ⟨hr₀, hc1, hc12, hs', _, hc2s, _⟩ := hV'
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : ℝ, σ₁ = C.bands.c₁ * C.bands.s' := ⟨_, rfl⟩
  obtain ⟨σ₂, hσ₂def⟩ : ∃ σ₂ : ℝ, σ₂ = C.bands.c₂ * C.bands.s' := ⟨_, rfl⟩
  have hσ₁ : 0 < σ₁ := by rw [hσ₁def]; exact mul_pos hc1 hs'
  have hσ12 : σ₁ < σ₂ := by rw [hσ₁def, hσ₂def]; exact mul_lt_mul_of_pos_right hc12 hs'
  have hσ₂ : σ₂ < 1 / 4 := by rw [hσ₂def]; exact hc2s
  -- Fourier coefficients of the cutoff and of `y ψ(y)`
  obtain ⟨a, hrep, _⟩ := cutoffRep_of C.psi hψs hψsupp
  have hψ₂s : ContDiff ℝ ∞ (fun y => y * C.psi y) := contDiff_id.mul hψs
  have hψ₂supp : Function.support (fun y => y * C.psi y) ⊆ Set.Icc 1 2 := by
    intro y hy
    apply hψsupp
    rw [Function.mem_support] at hy ⊢
    intro h0
    apply hy
    simp [h0]
  obtain ⟨a₂, hrep₂, hmom₂⟩ := cutoffRep_of _ hψ₂s hψ₂supp
  obtain ⟨A₁, hA₁def⟩ : ∃ A₁ : ℝ, A₁ = ∫ t, ‖a t‖ := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂def⟩ : ∃ A₂ : ℝ, A₂ = ∫ t, ‖a₂ t‖ := ⟨_, rfl⟩
  obtain ⟨Mom1, hMom1def⟩ : ∃ M : ℝ, M = ∫ t, ‖t‖ ^ 1 * ‖a₂ t‖ := ⟨_, rfl⟩
  have hA₁ : 0 ≤ A₁ := by rw [hA₁def]; exact integral_nonneg (fun _ => norm_nonneg _)
  have hA₂ : 0 ≤ A₂ := by rw [hA₂def]; exact integral_nonneg (fun _ => norm_nonneg _)
  have hMom1 : 0 ≤ Mom1 := by rw [hMom1def]; exact integral_nonneg (fun _ => by positivity)
  -- classical inputs
  obtain ⟨K, hK, hLSK⟩ := largeSieve_prim hc.largeSieve
  obtain ⟨c0, hc0, hd0⟩ := divisor_moment_L hc.divisors 0
  obtain ⟨c1, hc1', hd1⟩ := divisor_moment_L hc.divisors 1
  obtain ⟨c2, hc2', hd2⟩ := divisor_moment_L hc.divisors 2
  obtain ⟨E, hE, hβev⟩ := beta_divisor_bound C.bands hV
  obtain ⟨Kh, hKh, hHev⟩ := Erdos821.P7B.reciprocalTotientSquarefreeSum_eventually_le_log hc
  -- exponents
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = 4 + E + c2 / 2 + D := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 + C' + E + c1 + D := ⟨_, rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ B1 : ℝ, B1 = A + c0 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = C' + B1 + 1 := ⟨_, rfl⟩
  have hC'pos : 0 < C' := by rw [hC']; linarith
  have hApos : 0 < A := by rw [hA]; linarith
  have hB1pos : 0 < B1 := by rw [hB1]; linarith
  have hBpos : 0 < B := by rw [hBdef]; linarith
  obtain ⟨KHC, hKHC, hHC⟩ := hc.harmonic (1 / 2) 1 B A (by norm_num) one_pos hBpos hApos
  obtain ⟨cS, hcSdef⟩ : ∃ cS : ℝ, cS = θ / σ₁ := ⟨_, rfl⟩
  have hcS : 0 ≤ cS := by rw [hcSdef]; exact div_nonneg hθ0.le hσ₁.le
  -- the five final terms
  have evA : ∀ᶠ x : ℝ in atTop, (Kh * L x) * (L x ^ C' * (x * ((KHC * A₂ + Mom1) *
      L x ^ (-A)) * (2 * (L x ^ E * L x ^ c1)))) ≤ x * L x ^ (-D) := by
    filter_upwards [ev_small_log (2 * Kh * (KHC * A₂ + Mom1)) (1 + C' + -A + (E + c1)) D
      (by linarith), eventually_gt_atTop 1] with x h hx1
    have hL : 0 < L x := Real.log_pos hx1
    refine le_trans (le_of_eq ?_) h
    simp only [Real.rpow_add hL, Real.rpow_one]
    ring
  have evB : ∀ᶠ x : ℝ in atTop, (Kh * L x) * (L x ^ C' * (Mψ * cS *
      (4 * (L x ^ E * L x ^ c1) * x ^ (1 - σ₁)))) ≤ x * L x ^ (-D) := by
    filter_upwards [ev_small_power (4 * Kh * Mψ * cS) (1 + C' + (E + c1)) (1 - σ₁) D
      (by linarith), eventually_gt_atTop 1] with x h hx1
    have hL : 0 < L x := Real.log_pos hx1
    refine le_trans (le_of_eq ?_) h
    simp only [Real.rpow_add hL, Real.rpow_one]
    ring
  have evC : ∀ᶠ x : ℝ in atTop, (Kh * L x) * ((3 * L x) * (A₁ * ((3 * L x) *
      (2 * K * (6 * (L x ^ E * L x ^ (c2 / 2)) * x ^ (1 / 2 : ℝ)) *
        (3 * x ^ (1 / 2 : ℝ) / L x ^ C'))))) ≤ x * L x ^ (-D) := by
    filter_upwards [ev_small_log (324 * K * Kh * A₁) (1 + 1 + 1 + (E + c2 / 2) + -C') D
      (by linarith), eventually_gt_atTop 1] with x h hx1
    have hL : 0 < L x := Real.log_pos hx1
    have hx0 : 0 < x := by linarith
    have hxx : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
      rw [← Real.rpow_add hx0]; norm_num
    refine le_trans (le_of_eq ?_) h
    calc _ = 324 * K * Kh * A₁ * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) *
          L x ^ (1 + 1 + 1 + (E + c2 / 2) + -C') := by
          simp only [Real.rpow_add hL, Real.rpow_neg hL.le, Real.rpow_one]
          ring
      _ = _ := by rw [hxx]
  have evD : ∀ᶠ x : ℝ in atTop, (Kh * L x) * ((3 * L x) * (A₁ * ((3 * L x) *
      (2 * K * (6 * (L x ^ E * L x ^ (c2 / 2)) * x ^ (1 / 2 : ℝ)) *
        (2 * L x ^ (1 / 2 : ℝ) * (3 * x ^ ((1 - σ₁) / 2) + 3 * x ^ ((1 - σ₁) / 2))))))) ≤
      x * L x ^ (-D) := by
    filter_upwards [ev_small_power (1296 * K * Kh * A₁) (1 + 1 + 1 + (E + c2 / 2) + 1 / 2)
      (1 / 2 + (1 - σ₁) / 2) D (by linarith), eventually_gt_atTop 1] with x h hx1
    have hL : 0 < L x := Real.log_pos hx1
    have hx0 : 0 < x := by linarith
    refine le_trans (le_of_eq ?_) h
    simp only [Real.rpow_add hL, Real.rpow_add hx0, Real.rpow_one]
    ring
  have evE : ∀ᶠ x : ℝ in atTop, (Kh * L x) * ((3 * L x) * (A₁ * ((3 * L x) *
      (2 * K * (6 * (L x ^ E * L x ^ (c2 / 2)) * x ^ (1 / 2 : ℝ)) *
        (2 * x ^ θ * (2 * L x)))))) ≤ x * L x ^ (-D) := by
    filter_upwards [ev_small_power (432 * K * Kh * A₁) (1 + 1 + 1 + (E + c2 / 2) + 1)
      (1 / 2 + θ) D (by linarith), eventually_gt_atTop 1] with x h hx1
    have hL : 0 < L x := Real.log_pos hx1
    have hx0 : 0 < x := by linarith
    refine le_trans (le_of_eq ?_) h
    simp only [Real.rpow_add hL, Real.rpow_add hx0, Real.rpow_one]
    ring
  -- the main eventual estimate
  filter_upwards [eventually_gt_atTop 1, tendsto_L'.eventually (eventually_ge_atTop 8),
    band_zero_prime_free C.bands hV, hβev jstar, hd0, hd1, hd2,
    (tendsto_rpow_atTop hθ0).eventually hHev, hHC,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_L').eventually
      (eventually_ge_atTop (1 / σ₁)),
    evA, evB, evC, evD, evE] with x hx1 hL8 hband hβ hd0x hd1x hd2x hH hHCx hsqrtL
      hA' hB' hC'' hD' hE'
  have hx0 : 0 < x := by linarith
  have hL : 0 < L x := by linarith
  have hL1 : 1 ≤ L x := by linarith
  have hLx : L x = Real.log x := rfl
  simp only [Function.comp] at hsqrtL
  -- basic objects
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = x ^ θ := ⟨_, rfl⟩
  rw [← hXdef]
  have hX1 : 1 ≤ X := by rw [hXdef]; exact Real.one_le_rpow hx1.le hθ0.le
  have hXx : X ≤ x := by
    rw [hXdef]
    calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      _ = x := Real.rpow_one x
  set Q := ⌊X⌋₊ with hQdef
  have hQ1 : 1 ≤ Q := Nat.le_floor (by simpa using hX1)
  have hQX : (Q : ℝ) ≤ X := Nat.floor_le (by linarith)
  set R := ⌊L x ^ C'⌋₊ with hRdef
  have hLC' : 0 < L x ^ C' := Real.rpow_pos_of_pos hL _
  have hRle : (R : ℝ) ≤ L x ^ C' := Nat.floor_le hLC'.le
  have hRge : L x ^ C' ≤ (R : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  set s₀ := Erdos821.P7B.firstSlot C.bands x hr₀ with hs₀
  have hpure : C.bands.slotValues x jstar s₀ = C.bands.band x 0 :=
    Erdos821.P7B.firstSlot_is_pure C.bands x jstar hr₀ hjpos
  set lo := Real.exp (C.bands.c₁ * C.bands.scale x 0) with hlodef
  set hi := Real.exp (C.bands.c₂ * C.bands.scale x 0) with hhidef
  have hscale : C.bands.scale x 0 = C.bands.s' * L x := by
    simp [BandData.scale]
  have hloσ : C.bands.c₁ * C.bands.scale x 0 = σ₁ * L x := by rw [hscale, hσ₁def]; ring
  have hhiσ : C.bands.c₂ * C.bands.scale x 0 = σ₂ * L x := by rw [hscale, hσ₂def]; ring
  have hlo : lo = x ^ σ₁ := by
    rw [hlodef, hloσ, Real.rpow_def_of_pos hx0, hLx, mul_comm]
  have hhi : hi = x ^ σ₂ := by
    rw [hhidef, hhiσ, Real.rpow_def_of_pos hx0, hLx, mul_comm]
  have hlo1 : 1 < lo := by rw [hlo]; exact Real.one_lt_rpow hx1 hσ₁
  have hlo0 : 0 < lo := by linarith
  have hhix : hi ≤ x := by
    rw [hhi]
    calc x ^ σ₂ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      _ = x := Real.rpow_one x
  have hlogLo : Real.log lo = σ₁ * L x := by rw [hlodef, Real.log_exp, hloσ]
  have hxlo : x / lo = x ^ (1 - σ₁) := by
    rw [hlo, Real.rpow_sub hx0, Real.rpow_one]
  have hx1σ : 1 ≤ x ^ (1 - σ₁) := Real.one_le_rpow hx1.le (by linarith)
  have hσ₂le : x ^ σ₂ ≤ x ^ (1 - σ₁) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hplo : ∀ p ∈ C.bands.band x 0, lo ≤ p ∧ (p : ℝ) ≤ hi := fun p hp =>
    band_zero_bounds C.bands x p hp
  have hBs₀ : ∀ p ∈ C.bands.slotValues x jstar s₀,
      p.Prime ∧ S56Core.GroupFree (C.bands.groups x) p := by
    rw [hpure]; exact hband
  have hLsum : ∀ c : ℝ, 0 ≤ L x ^ c := fun c => Real.rpow_nonneg hL.le c
  have hxsum : ∀ c : ℝ, 0 ≤ x ^ c := fun c => Real.rpow_nonneg hx0.le c
  have hRHS0 : 0 ≤ x * L x ^ (-D) := mul_nonneg hx0.le (hLsum _)
  -- empty slot: everything vanishes
  by_cases hne : (C.bands.band x 0).Nonempty
  swap
  · have hempty : C.bands.slotValues x jstar s₀ = ∅ := by
      rw [hpure]; exact Finset.not_nonempty_iff_eq_empty.1 hne
    refine le_trans (typeI_character_reduction X (Finset.Icc 1 ⌊2 * x⌋₊) (C.weighted x jstar))
      ?_
    have hz : ∀ (Q' h : ℕ) (χ : CharacterIndex Q'),
        twisted (Finset.Icc 1 ⌊2 * x⌋₊) (C.weighted x jstar) h χ = 0 :=
      fun Q' h χ => twisted_zero_of_empty C x hx0 jstar s₀ hψsupp hempty Q' h χ
    simp only [hz, norm_zero, mul_zero, Finset.sum_const_zero]
    linarith
  obtain ⟨p₀, hp₀⟩ := hne
  have hp₀s : p₀ ∈ C.bands.slotValues x jstar s₀ := by rw [hpure]; exact hp₀
  have hβb : ∀ r : ℕ, 0 < r →
      beta C.bands x jstar s₀ r ≤ 2 * L x ^ E * (r.divisors.card : ℝ) :=
    hβ s₀ p₀ hp₀s (hband p₀ hp₀).1
  have hβ0 : ∀ r, 0 ≤ beta C.bands x jstar s₀ r := fun r => beta_nonneg C.bands x jstar s₀ r
  -- parameters for the deterministic bound
  set N₀ := ⌊2 * x / lo⌋₊ with hN₀def
  have hN₀ : (N₀ : ℝ) ≤ 2 * x ^ (1 - σ₁) := by
    calc (N₀ : ℝ) ≤ 2 * x / lo := Nat.floor_le (div_nonneg (by linarith) hlo0.le)
      _ = 2 * (x / lo) := by ring
      _ = 2 * x ^ (1 - σ₁) := by rw [hxlo]
  have hN₀x : (N₀ : ℝ) ≤ 4 * x := by
    have : x ^ (1 - σ₁) ≤ x := by
      calc x ^ (1 - σ₁) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        _ = x := Real.rpow_one x
    linarith
  have hN : ∀ p ∈ C.bands.slotValues x jstar s₀, ⌊2 * x⌋₊ / p ≤ N₀ := by
    intro p hp
    rw [hpure] at hp
    have hplo' := (hplo p hp).1
    have hp0 : (0 : ℝ) < p := by linarith
    apply Nat.le_floor
    calc ((⌊2 * x⌋₊ / p : ℕ) : ℝ) ≤ (⌊2 * x⌋₊ : ℝ) / p := Nat.cast_div_le
      _ ≤ 2 * x / p := div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) hp0.le
      _ ≤ 2 * x / lo := div_le_div_of_nonneg_left (by linarith) hlo0 hplo'
  have hSH : ∑ h ∈ Erdos821.P7B.squarefreeModuli X, (h.totient : ℝ)⁻¹ ≤ Kh * L x := by
    have h1 : Erdos821.P7B.reciprocalTotientSquarefreeSum (x ^ θ) ≤
        Kh * Real.log (x ^ θ) := hH
    rw [← hXdef] at h1
    unfold Erdos821.P7B.reciprocalTotientSquarefreeSum at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hKh.le)
    rw [hXdef, Real.log_rpow hx0, ← hLx]
    have : θ * L x ≤ 1 * L x := mul_le_mul_of_nonneg_right (by linarith) hL.le
    linarith
  have hcount : ∀ h ∈ Erdos821.P7B.squarefreeModuli X,
      (((C.bands.slotValues x jstar s₀).filter (fun p => ¬ Nat.Coprime p h)).card : ℝ) ≤ cS := by
    intro h hh
    obtain ⟨hhI, _⟩ := Finset.mem_filter.1 hh
    obtain ⟨hh1, hhX⟩ := Finset.mem_Icc.1 hhI
    rw [hpure]
    refine (card_large_prime_divisors (C.bands.band x 0) (fun p hp => (hband p hp).1) h hh1
      lo hlo1 (fun p hp => (hplo p hp).1)).trans ?_
    rw [hlogLo, hcSdef]
    have hlogh : Real.log h ≤ θ * L x := by
      have hhX' : (h : ℝ) ≤ X := (Nat.cast_le.2 hhX).trans hQX
      calc Real.log h ≤ Real.log X := Real.log_le_log (by exact_mod_cast hh1) hhX'
        _ = θ * L x := by rw [hXdef, Real.log_rpow hx0]; rfl
    have hσL : 0 < σ₁ * L x := mul_pos hσ₁ hL
    calc Real.log h / (σ₁ * L x) ≤ θ * L x / (σ₁ * L x) :=
          div_le_div_of_nonneg_right hlogh hσL.le
      _ = θ / σ₁ := by field_simp
  set T0 := L x ^ B1 with hT0def
  have hT0 : 0 < T0 := Real.rpow_pos_of_pos hL _
  set ε := KHC * L x ^ (-A) with hεdef
  have hε : 0 ≤ ε := mul_nonneg hKHC.le (hLsum _)
  set MH := L x ^ c0 with hMHdef
  have hMH0 : 0 ≤ MH := hLsum _
  have hband_sub : C.bands.band x 0 ⊆ Finset.Icc 1 ⌊hi⌋₊ := by
    intro p hp
    have hpI := (Finset.mem_filter.1 hp).1
    exact Finset.mem_Icc.2 ⟨(hband p hp).1.one_lt.le, (Finset.mem_Icc.1 hpI).2⟩
  have hMH : ∀ χ ∈ (primitiveCharacters Q).filter (fun χ => 1 < fC χ ∧ fC χ ≤ R), ∀ t,
      ‖∑ p ∈ C.bands.slotValues x jstar s₀, charValue χ p * tw p t / (p : ℂ)‖ ≤ MH := by
    intro χ _ t
    rw [hpure]
    calc ‖∑ p ∈ C.bands.band x 0, charValue χ p * tw p t / (p : ℂ)‖
        ≤ ∑ p ∈ C.bands.band x 0, ‖charValue χ p * tw p t / (p : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ C.bands.band x 0, (1 : ℝ) / p := by
          apply Finset.sum_le_sum
          intro p _
          rw [norm_div, norm_mul, tw_norm, mul_one, Complex.norm_natCast]
          exact div_le_div_of_nonneg_right (charValue_norm_le χ p) (Nat.cast_nonneg _)
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊hi⌋₊, (n.divisors.card : ℝ) ^ 0 / n := by
          simp only [pow_zero]
          apply Finset.sum_le_sum_of_subset_of_nonneg hband_sub
          intro _ _ _
          positivity
      _ ≤ MH := hd0x _ (by
          have : (⌊hi⌋₊ : ℝ) ≤ hi := Nat.floor_le (Real.exp_pos _).le
          linarith)
  have hsmall : ∀ χ ∈ (primitiveCharacters Q).filter (fun χ => 1 < fC χ ∧ fC χ ≤ R), ∀ t,
      ‖t‖ ≤ T0 →
      ‖∑ p ∈ C.bands.slotValues x jstar s₀, charValue χ p * tw p t / (p : ℂ)‖ ≤ ε := by
    intro χ hχ t ht
    obtain ⟨hprim, hf1, hfR⟩ := Finset.mem_filter.1 hχ
    rw [hpure]
    have hχ1 : χ.2 ≠ 1 := by
      intro h1
      have hp : χ.2.IsPrimitive := by
        simpa [primitiveCharacters] using hprim
      unfold DirichletCharacter.IsPrimitive at hp
      rw [h1, DirichletCharacter.conductor_one] at hp
      unfold fC at hf1
      omega
    have hlo_exp : Real.exp (L x ^ (1 / 2 : ℝ)) ≤ lo := by
      rw [hlodef, hloσ]
      apply Real.exp_le_exp.2
      have hsq : L x ^ (1 / 2 : ℝ) * L x ^ (1 / 2 : ℝ) = L x := by
        rw [← Real.rpow_add hL]; norm_num
      have h1 : 1 ≤ σ₁ * L x ^ (1 / 2 : ℝ) := by
        have := mul_le_mul_of_nonneg_left hsqrtL hσ₁.le
        rwa [mul_one_div_cancel hσ₁.ne'] at this
      calc L x ^ (1 / 2 : ℝ) = 1 * L x ^ (1 / 2 : ℝ) := by ring
        _ ≤ (σ₁ * L x ^ (1 / 2 : ℝ)) * L x ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (hLsum _)
        _ = σ₁ * L x := by rw [mul_assoc, hsq]
    have hlohi : lo ≤ hi := by
      rw [hlodef, hhidef, hloσ, hhiσ]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hσ12.le hL.le)
    have hhi1 : hi ≤ x ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hhix
    have hrB : (((χ.1.val + 1 : ℕ)) : ℝ) ≤ L x ^ B := by
      have hfR' : χ.1.val + 1 ≤ R := hfR
      have h1 : ((χ.1.val + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hfR'
      have h2 : L x ^ C' ≤ L x ^ B :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hBdef]; linarith)
      linarith
    have htB : |2 * Real.pi * t| ≤ L x ^ B := by
      have hpi : 2 * Real.pi ≤ L x := by have := Real.pi_le_four; linarith
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have ht' : |t| ≤ L x ^ B1 := by rw [← Real.norm_eq_abs]; exact ht
      calc 2 * Real.pi * |t| ≤ L x * L x ^ B1 :=
            mul_le_mul hpi ht' (abs_nonneg _) hL.le
        _ = L x ^ (B1 + 1) := by rw [Real.rpow_add hL, Real.rpow_one]; ring
        _ ≤ L x ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hBdef]; linarith)
    exact hHCx lo hi (2 * Real.pi * t) (χ.1.val + 1) χ.2 hlo_exp hlohi hhi1
      (Nat.le_add_left 1 _) hrB hχ1 htB
  -- dyadic data
  set M := ⌊2 * x⌋₊ with hMdef
  have hM : (M : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
  set βB : ℕ → ℝ := fun k => ∑ r ∈ Finset.Icc 1 (M / 2 ^ k), (beta C.bands x jstar s₀ r) ^ 2
    with hβBdef
  have hβB : ∀ k, ∑ r ∈ Finset.Icc 1 (M / 2 ^ k), (beta C.bands x jstar s₀ r) ^ 2 ≤ βB k :=
    fun k => le_refl _
  set BBm := 2 * K * (6 * (L x ^ E * L x ^ (c2 / 2)) * x ^ (1 / 2 : ℝ)) *
    (3 * x ^ (1 / 2 : ℝ) / L x ^ C' +
      2 * L x ^ (1 / 2 : ℝ) * (3 * x ^ ((1 - σ₁) / 2) + 3 * x ^ ((1 - σ₁) / 2)) +
      2 * x ^ θ * (2 * L x)) with hBBmdef
  have hBB0 : 0 ≤ BBm := by
    apply mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK.le)
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hLsum _) (hLsum _))) (hxsum _)))
    apply add_nonneg (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (hxsum _)) hLC'.le)
      (mul_nonneg (mul_nonneg (by norm_num) (hLsum _))
        (add_nonneg (mul_nonneg (by norm_num) (hxsum _)) (mul_nonneg (by norm_num) (hxsum _)))))
    exact mul_nonneg (mul_nonneg (by norm_num) (hxsum _)) (mul_nonneg (by norm_num) hL.le)
  have hlog4Q : Real.log (4 * Q) ≤ 2 * L x := by
    have hQ0 : (0 : ℝ) < 4 * Q := by
      have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
      linarith
    have hlog4 : Real.log 4 ≤ L x := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc Real.log (4 * Q) ≤ Real.log (4 * x) := Real.log_le_log hQ0 (by linarith)
      _ = Real.log 4 + L x := by rw [Real.log_mul (by norm_num) hx0.ne']; rfl
      _ ≤ 2 * L x := by linarith
  have hBB : ∀ k ∈ (C.bands.slotValues x jstar s₀).image (Nat.log 2),
      blockBB K Q R (2 ^ (k + 1)) (M / 2 ^ k) (βB k) ≤ BBm := by
    intro k hk
    rw [hpure] at hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
    have hpp := (hband p hp).1
    obtain ⟨hplo', hphi'⟩ := hplo p hp
    have hp2k : 2 ^ (Nat.log 2 p) ≤ p := Nat.pow_log_le_self 2 hpp.ne_zero
    have hp2k1 : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
    set k := Nat.log 2 p with hkdef
    set NA : ℕ := 2 ^ (k + 1) with hNAdef
    set NB : ℕ := M / 2 ^ k with hNBdef
    have h2k0 : (0 : ℝ) < 2 ^ k := by positivity
    have hNA : (NA : ℝ) ≤ 2 * hi := by
      have : NA ≤ 2 * p := by rw [hNAdef, pow_succ]; omega
      have : (NA : ℝ) ≤ 2 * p := by exact_mod_cast this
      linarith
    have hNB : (NB : ℝ) ≤ 4 * x / lo := by
      have hlo2 : lo < 2 * (2 : ℝ) ^ k := by
        have : (p : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hp2k1
        push_cast at this
        rw [pow_succ] at this
        linarith
      calc (NB : ℝ) ≤ (M : ℝ) / ((2 ^ k : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ 2 * x / (2 : ℝ) ^ k := by
            push_cast
            exact div_le_div_of_nonneg_right hM h2k0.le
        _ ≤ 2 * x / (lo / 2) := div_le_div_of_nonneg_left (by linarith) (by linarith)
            (by linarith)
        _ = 4 * x / lo := by rw [div_div_eq_mul_div]; ring
    have hNBM : (NB : ℝ) ≤ 2 * x := by
      have : NB ≤ M := Nat.div_le_self M _
      have : (NB : ℝ) ≤ M := by exact_mod_cast this
      linarith
    have hNANB : (NA : ℝ) * NB ≤ 4 * x := by
      have : NA * NB ≤ 2 * M := by
        rw [hNAdef, hNBdef, pow_succ]
        calc 2 ^ k * 2 * (M / 2 ^ k) = 2 * (2 ^ k * (M / 2 ^ k)) := by ring
          _ ≤ 2 * M := Nat.mul_le_mul_left 2 (Nat.mul_div_le M _)
      have : (NA : ℝ) * NB ≤ 2 * M := by exact_mod_cast this
      linarith
    have hNAx : (NA : ℝ) ≤ 2 * x := by linarith
    have hprod9 : ((NA : ℝ) + 1) * ((NB : ℝ) + 1) ≤ 9 * x := by
      have e : ((NA : ℝ) + 1) * ((NB : ℝ) + 1) = (NA : ℝ) * NB + NA + NB + 1 := by ring
      linarith only [e, hNANB, hNAx, hNBM, hx1]
    have hβBk : βB k ≤ 4 * (L x ^ E) ^ 2 * ((NB : ℝ) * L x ^ c2) := by
      have hsq : ∀ r ∈ Finset.Icc 1 NB, (beta C.bands x jstar s₀ r) ^ 2 ≤
          4 * (L x ^ E) ^ 2 * (r.divisors.card : ℝ) ^ 2 := by
        intro r hr
        have hr0 : 0 < r := (Finset.mem_Icc.1 hr).1
        have := pow_le_pow_left₀ (hβ0 r) (hβb r hr0) 2
        calc (beta C.bands x jstar s₀ r) ^ 2 ≤ (2 * L x ^ E * (r.divisors.card : ℝ)) ^ 2 := this
          _ = 4 * (L x ^ E) ^ 2 * (r.divisors.card : ℝ) ^ 2 := by ring
      calc βB k = ∑ r ∈ Finset.Icc 1 NB, (beta C.bands x jstar s₀ r) ^ 2 := rfl
        _ ≤ ∑ r ∈ Finset.Icc 1 NB, 4 * (L x ^ E) ^ 2 * (r.divisors.card : ℝ) ^ 2 :=
            Finset.sum_le_sum hsq
        _ = 4 * (L x ^ E) ^ 2 * ∑ r ∈ Finset.Icc 1 NB, (r.divisors.card : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ 4 * (L x ^ E) ^ 2 * ((NB : ℝ) * L x ^ c2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine (sum_le_mul_sum_div NB _ (fun _ => by positivity)).trans ?_
            exact mul_le_mul_of_nonneg_left (hd2x NB (by linarith)) (Nat.cast_nonneg _)
    have hLc2sq : (L x ^ (c2 / 2)) ^ 2 = L x ^ c2 := rpow_div_two_sq hL.le c2
    apply bb_le K hK.le Q R NA NB hQ1 (βB k) (6 * (L x ^ E * L x ^ (c2 / 2)) * x ^ (1 / 2 : ℝ))
      (3 * x ^ (1 / 2 : ℝ)) (L x ^ C') (2 * L x ^ (1 / 2 : ℝ)) (3 * x ^ ((1 - σ₁) / 2))
      (2 * x ^ θ * (2 * L x))
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hLsum _) (hLsum _))) (hxsum _))
      (mul_nonneg (by norm_num) (hxsum _)) hLC' (mul_nonneg (by norm_num) (hLsum _))
      (mul_nonneg (by norm_num) (hxsum _))
    · rw [mul_pow, mul_pow, mul_pow, hLc2sq, rpow_half_sq hx0.le]
      have hNB0 : (0 : ℝ) ≤ NB := Nat.cast_nonneg _
      have hA1 : (0 : ℝ) ≤ (NA : ℝ) + 1 := by positivity
      have hk1 : ((NA : ℝ) + 1) * NB ≤ 9 * x := by
        have e : ((NA : ℝ) + 1) * NB = (NA : ℝ) * NB + NB := by ring
        linarith only [e, hNANB, hNBM, hx1]
      calc ((NA : ℝ) + 1) * βB k ≤ ((NA : ℝ) + 1) * (4 * (L x ^ E) ^ 2 * ((NB : ℝ) * L x ^ c2)) :=
            mul_le_mul_of_nonneg_left hβBk hA1
        _ = 4 * (L x ^ E) ^ 2 * L x ^ c2 * (((NA : ℝ) + 1) * NB) := by ring
        _ ≤ 4 * (L x ^ E) ^ 2 * L x ^ c2 * (9 * x) :=
            mul_le_mul_of_nonneg_left hk1 (mul_nonneg (by positivity) (hLsum c2))
        _ = 6 ^ 2 * ((L x ^ E) ^ 2 * L x ^ c2) * x := by ring
    · rw [mul_pow, rpow_half_sq hx0.le]
      linarith
    · exact hRge
    · rw [mul_pow, rpow_half_sq hL.le]
      linarith
    · rw [mul_pow, rpow_div_two_sq hx0.le]
      have : hi ≤ x ^ (1 - σ₁) := by rw [hhi]; exact hσ₂le
      linarith
    · rw [mul_pow, rpow_div_two_sq hx0.le]
      have : (NB : ℝ) ≤ 4 * x ^ (1 - σ₁) := by
        calc (NB : ℝ) ≤ 4 * x / lo := hNB
          _ = 4 * (x / lo) := by ring
          _ = 4 * x ^ (1 - σ₁) := by rw [hxlo]
      linarith
    · have hlog0 : 0 ≤ Real.log (4 * (Q : ℝ)) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
        linarith)
      calc 2 * (Q : ℝ) * Real.log (4 * Q) ≤ 2 * x ^ θ * (2 * L x) :=
            mul_le_mul (by rw [← hXdef]; linarith) hlog4Q hlog0
              (mul_nonneg (by norm_num) (hxsum θ))
        _ = _ := rfl
  -- apply the deterministic bound
  have hdet := deterministic_bound C x hx0 jstar s₀ hBs₀ hψsupp Mψ hMψabs a a₂ hrep hrep₂
    K hK.le hLSK X hX1 R (Kh * L x) hSH N₀ hN cS hcS hcount T0 ε MH hε hMH0 hMH hsmall βB hβB
    BBm hBB0 hBB
  refine le_trans hdet ?_
  -- bound the small-conductor sum
  set SB := ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r *
    ((x / r) * (ε * (∫ t, ‖a₂ t‖) + MH * ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖) + Mψ * cS)
    with hSBdef
  have htail : (∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖) ≤ (T0 ^ 1)⁻¹ * Mom1 := by
    rw [hMom1def]
    exact S56Core.fourier_tail_le_moment a₂ hrep₂.1 1 (hmom₂ 1) T0 hT0
  have htail0 : 0 ≤ ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖ :=
    setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => norm_nonneg _))
  have hΔ : ε * (∫ t, ‖a₂ t‖) + MH * ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖ ≤
      (KHC * A₂ + Mom1) * L x ^ (-A) := by
    have hMHT : MH * (T0 ^ 1)⁻¹ = L x ^ (-A) := by
      rw [hMHdef, hT0def, pow_one, ← Real.rpow_neg hL.le, ← Real.rpow_add hL, hB1]
      congr 1
      ring
    calc ε * (∫ t, ‖a₂ t‖) + MH * ∫ t in {t : ℝ | T0 < ‖t‖}, ‖a₂ t‖
        ≤ ε * A₂ + MH * ((T0 ^ 1)⁻¹ * Mom1) := by
          rw [← hA₂def]
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left htail hMH0)
      _ = (KHC * A₂ + Mom1) * L x ^ (-A) := by
          rw [← mul_assoc, hMHT, hεdef]
          ring
  have hSig1 : ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r / r ≤ 2 * (L x ^ E * L x ^ c1) := by
    calc ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r / r
        ≤ ∑ r ∈ Finset.Icc 1 N₀, 2 * L x ^ E * ((r.divisors.card : ℝ) ^ 1 / r) := by
          apply Finset.sum_le_sum
          intro r hr
          have hr0 : 0 < r := (Finset.mem_Icc.1 hr).1
          rw [pow_one, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right (hβb r hr0) (Nat.cast_nonneg _)
      _ = 2 * L x ^ E * ∑ r ∈ Finset.Icc 1 N₀, (r.divisors.card : ℝ) ^ 1 / r := by
          rw [Finset.mul_sum]
      _ ≤ 2 * L x ^ E * L x ^ c1 :=
          mul_le_mul_of_nonneg_left (hd1x N₀ hN₀x) (mul_nonneg (by norm_num) (hLsum _))
      _ = 2 * (L x ^ E * L x ^ c1) := by ring
  have hSig0 : ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r ≤
      4 * (L x ^ E * L x ^ c1) * x ^ (1 - σ₁) := by
    calc ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r
        ≤ (N₀ : ℝ) * ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r / r :=
          sum_le_mul_sum_div N₀ _ hβ0
      _ ≤ (2 * x ^ (1 - σ₁)) * (2 * (L x ^ E * L x ^ c1)) :=
          mul_le_mul hN₀ hSig1 (Finset.sum_nonneg (fun r _ => div_nonneg (hβ0 r) (Nat.cast_nonneg _)))
            (mul_nonneg (by norm_num) (hxsum _))
      _ = 4 * (L x ^ E * L x ^ c1) * x ^ (1 - σ₁) := by ring
  have hSB : SB ≤ x * ((KHC * A₂ + Mom1) * L x ^ (-A)) * (2 * (L x ^ E * L x ^ c1)) +
      Mψ * cS * (4 * (L x ^ E * L x ^ c1) * x ^ (1 - σ₁)) := by
    have hΔ0 : 0 ≤ (KHC * A₂ + Mom1) * L x ^ (-A) :=
      mul_nonneg (add_nonneg (mul_nonneg hKHC.le hA₂) hMom1) (hLsum _)
    calc SB ≤ ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r *
          ((x / r) * ((KHC * A₂ + Mom1) * L x ^ (-A)) + Mψ * cS) := by
          apply Finset.sum_le_sum
          intro r _
          apply mul_le_mul_of_nonneg_left _ (hβ0 r)
          exact add_le_add (mul_le_mul_of_nonneg_left hΔ (div_nonneg hx0.le (Nat.cast_nonneg _)))
            le_rfl
      _ = x * ((KHC * A₂ + Mom1) * L x ^ (-A)) *
            ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r / r +
          Mψ * cS * ∑ r ∈ Finset.Icc 1 N₀, beta C.bands x jstar s₀ r := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun r hr => ?_)
          ring
      _ ≤ x * ((KHC * A₂ + Mom1) * L x ^ (-A)) * (2 * (L x ^ E * L x ^ c1)) +
          Mψ * cS * (4 * (L x ^ E * L x ^ c1) * x ^ (1 - σ₁)) :=
          add_le_add (mul_le_mul_of_nonneg_left hSig1 (mul_nonneg hx0.le hΔ0))
            (mul_le_mul_of_nonneg_left hSig0 (mul_nonneg hMψ0 hcS))
  have hSB0 : 0 ≤ SB := by
    apply Finset.sum_nonneg
    intro r _
    apply mul_nonneg (hβ0 r)
    apply add_nonneg _ (mul_nonneg hMψ0 hcS)
    apply mul_nonneg (div_nonneg hx0.le (Nat.cast_nonneg _))
    exact add_nonneg (mul_nonneg hε (integral_nonneg (fun _ => norm_nonneg _)))
      (mul_nonneg hMH0 htail0)
  -- counts
  have hKs : (((C.bands.slotValues x jstar s₀).image (Nat.log 2)).card : ℝ) ≤ 3 * L x := by
    rw [hpure]
    have hsub : (C.bands.band x 0).image (Nat.log 2) ⊆ Finset.range (Nat.log 2 ⌊x⌋₊ + 1) := by
      intro k hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
      apply Finset.mem_range.2
      apply Nat.lt_succ_of_le
      apply Nat.log_mono_right
      apply Nat.le_floor
      exact (hplo p hp).2.trans hhix
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    have h2 : ((Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ 3 * L x :=
      natLog_add_one_le x hx1 hL1 ⌊x⌋₊ (Nat.floor_le hx0.le)
    have : (((C.bands.band x 0).image (Nat.log 2)).card : ℝ) ≤ ((Nat.log 2 ⌊x⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this
    linarith
  have hJ : ((((Finset.range (Nat.log 2 Q + 1)).filter (fun j => R < 2 ^ (j + 1))).card : ℕ) : ℝ)
      ≤ 3 * L x := by
    have h1 := Finset.card_filter_le (Finset.range (Nat.log 2 Q + 1)) (fun j => R < 2 ^ (j + 1))
    rw [Finset.card_range] at h1
    have h2 : ((Nat.log 2 Q : ℕ) : ℝ) + 1 ≤ 3 * L x :=
      natLog_add_one_le x hx1 hL1 Q (hQX.trans hXx)
    have : ((((Finset.range (Nat.log 2 Q + 1)).filter (fun j => R < 2 ^ (j + 1))).card : ℕ) : ℝ)
        ≤ ((Nat.log 2 Q + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  -- assemble
  have hKL : 0 ≤ Kh * L x := mul_nonneg hKh.le hL.le
  have hY1 : (R : ℝ) * SB ≤ L x ^ C' * (x * ((KHC * A₂ + Mom1) * L x ^ (-A)) *
      (2 * (L x ^ E * L x ^ c1)) + Mψ * cS * (4 * (L x ^ E * L x ^ c1) * x ^ (1 - σ₁))) :=
    mul_le_mul hRle hSB hSB0 hLC'.le
  have hY2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJ hBB0) hA₁
  have hY3 := mul_le_mul hKs hY2 (mul_nonneg hA₁ (mul_nonneg (Nat.cast_nonneg _) hBB0))
    (by linarith)
  have hYsum := add_le_add hY1 hY3
  have hYfin := mul_le_mul_of_nonneg_left hYsum hKL
  rw [hA₁def] at hYfin
  refine le_trans hYfin ?_
  rw [← hA₁def]
  have hsplit : (Kh * L x) * (L x ^ C' * (x * ((KHC * A₂ + Mom1) * L x ^ (-A)) *
      (2 * (L x ^ E * L x ^ c1)) + Mψ * cS * (4 * (L x ^ E * L x ^ c1) * x ^ (1 - σ₁))) +
      3 * L x * (A₁ * (3 * L x * BBm))) =
    (Kh * L x) * (L x ^ C' * (x * ((KHC * A₂ + Mom1) * L x ^ (-A)) *
      (2 * (L x ^ E * L x ^ c1)))) +
    (Kh * L x) * (L x ^ C' * (Mψ * cS * (4 * (L x ^ E * L x ^ c1) * x ^ (1 - σ₁)))) +
    (Kh * L x) * ((3 * L x) * (A₁ * ((3 * L x) *
      (2 * K * (6 * (L x ^ E * L x ^ (c2 / 2)) * x ^ (1 / 2 : ℝ)) *
        (3 * x ^ (1 / 2 : ℝ) / L x ^ C'))))) +
    (Kh * L x) * ((3 * L x) * (A₁ * ((3 * L x) *
      (2 * K * (6 * (L x ^ E * L x ^ (c2 / 2)) * x ^ (1 / 2 : ℝ)) *
        (2 * L x ^ (1 / 2 : ℝ) * (3 * x ^ ((1 - σ₁) / 2) + 3 * x ^ ((1 - σ₁) / 2))))))) +
    (Kh * L x) * ((3 * L x) * (A₁ * ((3 * L x) *
      (2 * K * (6 * (L x ^ E * L x ^ (c2 / 2)) * x ^ (1 / 2 : ℝ)) *
        (2 * x ^ θ * (2 * L x)))))) := by
    rw [hBBmdef]
    ring
  linarith only [hsplit, hA', hB', hC'', hD', hE']

theorem nonprincipalTypeITask_proof : NonprincipalTypeITask := by
  intro hc δ C hC _hb θ D hθ hD jstar hj
  set θ' := max θ (1 / 4) with hθ'def
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hθ'1 : θ' < 1 / 2 := max_lt hθ (by norm_num)
  refine ⟨5, by norm_num, ?_⟩
  filter_upwards [main_bound hc δ C hC θ' D hθ'0 hθ'1 hD jstar hj, eventually_ge_atTop 1]
    with x hx hx1
  refine le_trans ?_ hx
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [oddSqfreeModuli, Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    refine ⟨⟨hd.1.1, hd.1.2.trans (Nat.floor_mono ?_)⟩, hd.2⟩
    exact Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  · intro _ _ _
    exact abs_nonneg _


end Erdos821.P7Char
