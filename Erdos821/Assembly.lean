import Erdos821.Challenge
import Erdos821.Supply
import OAI.NumberTheory.TotientFibers.FiniteFiber

open Filter

namespace Erdos821

private theorem g_eq_oai_g_of_pos {n : ℕ} (hn : 0 < n) :
    Erdos821.g n = OAI.TotientFibers.g n := by
  classical
  have hset : ({m : ℕ | Nat.totient m = n} : Set ℕ) =
      {m : ℕ | 0 < m ∧ Nat.totient m = n} := by
    ext m
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hm
      exact ⟨Nat.totient_pos.mp (hm ▸ hn), hm⟩
    · intro hm
      exact hm.2
  unfold Erdos821.g OAI.TotientFibers.g OAI.TotientFibers.fiber
  rw [hset]

private theorem statement_of_supply_small_epsilon
    (h : SmoothShiftedPrimeSupply) {ε : ℝ} (hεpos : 0 < ε) (hεle : ε ≤ 1) :
    {n : ℕ | 0 < n ∧ (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  classical
  obtain ⟨a, ha⟩ := exists_nat_gt (4 / ε)
  have haε : 4 ≤ (a : ℝ) * ε := by
    have hmul : 4 < (a : ℝ) * ε := (div_lt_iff₀ hεpos).mp ha
    linarith
  have hratio : (4 : ℝ) ≤ 4 / ε := (le_div_iff₀ hεpos).2 (by nlinarith)
  have ha5 : 5 ≤ a := by
    have hfour : 4 < a := by exact_mod_cast hratio.trans_lt ha
    omega

  let δ : ℝ := 1 / (4 * (a : ℝ))
  let σ : ℝ := δ
  have haReal : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδlt : δ < 1 / 4 := by
    dsimp [δ]
    have hane : (a : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith [haReal]
  have hσpos : 0 < σ := by simpa [σ] using hδpos
  have hadelta : (a : ℝ) * δ = 1 / 4 := by
    dsimp [δ]
    have hane : (a : ℝ) ≠ 0 := by positivity
    field_simp
  have hadeltaσ : (a : ℝ) * σ = 1 / 4 := by simpa [σ] using hadelta

  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 (h δ hδpos hδlt σ hσpos)
  have hUnbounded : ∀ B : ℕ, ∃ n : ℕ, 0 < n ∧
      (n : ℝ) ^ (1 - ε) < (g n : ℝ) ∧
      B < OAI.TotientFibers.g n := by
    intro B
    let M : ℝ := max X (max ((B : ℝ) + 30) ((a : ℝ) + 1))
    obtain ⟨u, hu⟩ := exists_nat_gt M
    have hXM : X ≤ M := le_max_left X _
    have hBM : (B : ℝ) ≤ M := by
      calc
        (B : ℝ) ≤ (B : ℝ) + 30 := by norm_num
        _ ≤ max ((B : ℝ) + 30) ((a : ℝ) + 1) := le_max_left _ _
        _ ≤ M := le_max_right _ _
    have haM : (a : ℝ) + 1 ≤ M := by
      calc
        (a : ℝ) + 1 ≤ max ((B : ℝ) + 30) ((a : ℝ) + 1) := le_max_right _ _
        _ ≤ M := le_max_right _ _
    have h25M : (25 : ℝ) ≤ M := by
      calc
        (25 : ℝ) ≤ (B : ℝ) + 30 := by nlinarith
        _ ≤ max ((B : ℝ) + 30) ((a : ℝ) + 1) := le_max_left _ _
        _ ≤ M := le_max_right _ _
    have hXlt : X < (u : ℝ) := hXM.trans_lt hu
    have hBlt : (B : ℝ) < (u : ℝ) := hBM.trans_lt hu
    have haLt : (a : ℝ) < (u : ℝ) := by linarith [haM, hu]
    have h25lt : (25 : ℝ) < (u : ℝ) := h25M.trans_lt hu
    have hBu : B < u := by exact_mod_cast hBlt
    have haU : a < u := by exact_mod_cast haLt
    have h25u : 25 < u := by exact_mod_cast h25lt

    let T : ℕ := u ^ 4
    let x : ℝ := (T : ℝ) ^ a / 5
    let P : Finset ℕ := smoothShiftedPrimes δ x
    have huT : u ≤ T := by
      dsimp [T]
      simpa only [pow_one] using
        (pow_le_pow_right₀ (by omega : 1 ≤ u) (by decide : 1 ≤ 4))
    have haT : a ≤ T := (Nat.le_of_lt haU).trans huT
    have hT5 : 5 ≤ T := ha5.trans haT
    have hTpos : 0 < T := by omega
    have hTpow : T ^ 2 ≤ T ^ a :=
      pow_le_pow_right₀ (by omega : 1 ≤ T) (by omega : 2 ≤ a)
    have h5T2 : 5 * T ≤ T ^ 2 := by
      rw [pow_two]
      nlinarith [Nat.mul_le_mul_left T hT5]
    have h5Tpow : 5 * T ≤ T ^ a := h5T2.trans hTpow
    have hxT : (T : ℝ) ≤ x := by
      dsimp [x]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2
      have h5Tpow' : T * 5 ≤ T ^ a := by
        simpa [Nat.mul_comm] using h5Tpow
      exact_mod_cast h5Tpow'
    have hXT : X ≤ (T : ℝ) := by
      calc
        X ≤ (u : ℝ) := le_of_lt hXlt
        _ ≤ T := by exact_mod_cast huT
    have hXx : X ≤ x := hXT.trans hxT

    have hcount0 : x ^ (1 - σ) ≤ (P.card : ℝ) := by
      dsimp [P]
      exact hX x hXx

    have hPinterval {p : ℕ} (hp : p ∈ P) :
        p ∈ Finset.Ioc ⌊2 * x⌋₊ ⌊5 * x⌋₊ := by
      dsimp [P, smoothShiftedPrimes] at hp
      exact (Finset.mem_filter.mp hp).1
    have hPdata {p : ℕ} (hp : p ∈ P) :
        p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ δ := by
      dsimp [P, smoothShiftedPrimes] at hp
      exact (Finset.mem_filter.mp hp).2
    have hprime : ∀ p ∈ P, p.Prime := fun p hp => (hPdata hp).1

    have hsize : ∀ p ∈ P, p ≤ T ^ a := by
      intro p hp
      have hpupperNat := (Finset.mem_Ioc.mp (hPinterval hp)).2
      have hpupper : (p : ℝ) ≤ (T : ℝ) ^ a := by
        calc
          (p : ℝ) ≤ (⌊5 * x⌋₊ : ℝ) := by exact_mod_cast hpupperNat
          _ ≤ 5 * x := Nat.floor_le (by positivity)
          _ = (T : ℝ) ^ a := by dsimp [x]; ring
      exact_mod_cast hpupper

    have hxupper : x ≤ (T : ℝ) ^ a := by
      dsimp [x]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)]
      have hp : 0 ≤ (T : ℝ) ^ a := by positivity
      nlinarith
    have hxδ : x ^ δ ≤ (T : ℝ) := by
      calc
        x ^ δ ≤ ((T : ℝ) ^ a) ^ δ :=
          Real.rpow_le_rpow (by positivity) hxupper hδpos.le
        _ = (T : ℝ) ^ ((a : ℝ) * δ) := by
          rw [← Real.rpow_natCast_mul (Nat.cast_nonneg T)]
        _ = (T : ℝ) ^ (1 / 4 : ℝ) := by rw [hadelta]
        _ ≤ (T : ℝ) ^ (1 : ℝ) := by
          have hToneR : (1 : ℝ) ≤ (T : ℝ) := by
            exact_mod_cast (show 1 ≤ T by omega)
          exact Real.rpow_le_rpow_of_exponent_le hToneR (by norm_num)
        _ = (T : ℝ) := by simp
    have hsmooth : ∀ p ∈ P, ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ≤ T := by
      intro p hp q hq hdiv
      have hqreal := (hPdata hp).2 q hq hdiv
      exact_mod_cast hqreal.trans hxδ

    let k : ℕ := 4 * a - 1
    have hkplus : k + 1 = 4 * a := by dsimp [k]; omega
    have hkpos : 1 ≤ k := by dsimp [k]; omega
    have hkReal : (k : ℝ) + 1 = 4 * (a : ℝ) := by exact_mod_cast hkplus
    have hdenpos : 0 < 4 * (a : ℝ) := by positivity
    have hkfrac : (k : ℝ) / (4 * (a : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ hdenpos).2
      rw [← hkReal]
      linarith
    have hkexp : (k : ℝ) - 1 ≤ (k : ℝ) * (1 - σ) := by
      have heq : (k : ℝ) * (1 - σ) = (k : ℝ) - (k : ℝ) / (4 * (a : ℝ)) := by
        dsimp [σ, δ]
        field_simp
      rw [heq]
      linarith
    have hTthreshold : T ^ (a - 1) < u ^ (k - 1) := by
      rw [show T = u ^ 4 by rfl, ← pow_mul]
      apply pow_lt_pow_right₀ (by omega : 1 < u)
      have : 4 * (a - 1) < k - 1 := by dsimp [k]; omega
      exact this
    have hpowlower : (u : ℝ) ^ ((k : ℝ) - 1) = ((u ^ (k - 1) : ℕ) : ℝ) := by
      rw [show (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        norm_num,
        Real.rpow_natCast]
      simp [Nat.cast_pow]
    have htrans : ((u ^ k : ℕ) : ℝ) ^ (1 - σ) =
        (u : ℝ) ^ ((k : ℝ) * (1 - σ)) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg u)]
    have hxlower : ((u ^ k : ℕ) : ℝ) ≤ x := by
      have hTcast : (T : ℝ) = (u : ℝ) ^ 4 := by simp [T, Nat.cast_pow]
      have hTpowcast : (T : ℝ) ^ a = (u : ℝ) ^ (4 * a) := by
        rw [hTcast, ← pow_mul]
      calc
        ((u ^ k : ℕ) : ℝ) = (u : ℝ) ^ k := by simp
        _ ≤ (u : ℝ) ^ (4 * a) / 5 := by
          rw [show 4 * a = k + 1 by omega, pow_succ]
          apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2
          have hu5 : (5 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : 5 ≤ u)
          have huk : 0 ≤ (u : ℝ) ^ k := by positivity
          nlinarith
        _ = x := by dsimp [x]; rw [← hTpowcast]
    have hpowexp : (u : ℝ) ^ ((k : ℝ) - 1) ≤
        (u : ℝ) ^ ((k : ℝ) * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ u by omega)) hkexp
    have hcount : (T : ℝ) ^ (a - 1) < x ^ (1 - σ) := by
      calc
        (T : ℝ) ^ (a - 1) < ((u ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hTthreshold
        _ = (u : ℝ) ^ ((k : ℝ) - 1) := hpowlower.symm
        _ ≤ (u : ℝ) ^ ((k : ℝ) * (1 - σ)) := hpowexp
        _ = ((u ^ k : ℕ) : ℝ) ^ (1 - σ) := htrans.symm
        _ ≤ x ^ (1 - σ) :=
          Real.rpow_le_rpow (by positivity) hxlower (by linarith [hδlt])
    have hcard : T ^ (a - 1) < P.card := by
      exact_mod_cast hcount.trans_le hcount0

    obtain ⟨n, hn, htn, hlarge⟩ := OAI.TotientFibers.finite_large_fiber_rpow
      (t := T) (a := a) (ε := ε) ha5 haT hεle haε hprime hsize hsmooth hcard
    have hBT : B < T := lt_of_lt_of_le hBu huT
    have hBgt : B < OAI.TotientFibers.g n := lt_trans hBT htn
    have hEq := g_eq_oai_g_of_pos hn
    have hlarge' : (n : ℝ) ^ (1 - ε) < (g n : ℝ) := by rw [hEq]; exact hlarge
    exact ⟨n, hn, hlarge', hBgt⟩

  have hInfinite := OAI.TotientFibers.infinite_of_unbounded_g
    (P := fun n => (n : ℝ) ^ (1 - ε) < (g n : ℝ)) hUnbounded
  exact hInfinite

theorem statement_of_supply (h : SmoothShiftedPrimeSupply) : Statement := by
  intro ε hε
  let ε₀ : ℝ := min ε 1
  have hε₀pos : 0 < ε₀ := by dsimp [ε₀]; exact lt_min hε (by norm_num)
  have hε₀le : ε₀ ≤ 1 := by dsimp [ε₀]; exact min_le_right _ _
  have hε₀ε : ε₀ ≤ ε := by dsimp [ε₀]; exact min_le_left _ _
  have hInfinite := statement_of_supply_small_epsilon h hε₀pos hε₀le
  apply hInfinite.mono
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hexp : 1 - ε ≤ 1 - ε₀ := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  exact hpow.trans_lt hn.2


end Erdos821
