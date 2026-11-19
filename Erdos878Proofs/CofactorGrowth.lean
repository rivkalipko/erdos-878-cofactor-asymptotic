module

public import Erdos878Proofs.CofactorIntervals

@[expose] public section

/-! # Growth of the polynomial count in the cofactor construction -/

open Filter Asymptotics
open scoped Topology

namespace Erdos878

private theorem log_exponent_bound {x : ℕ} (hx : 2 ≤ x) (hT : 3 ≤ Real.log (x : ℝ)) :
    Real.log ((Nat.log 2 x + 1 : ℕ) : ℝ) ≤ 2 * Real.log (Real.log (x : ℝ)) := by
  let T := Real.log (x : ℝ)
  have hT' : 3 ≤ T := hT
  have hTpos : 0 < T := by linarith
  have hx0 : x ≠ 0 := by omega
  have hlog₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hpow : (2 : ℝ) ^ Nat.log 2 x ≤ (x : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hx0
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  have hB : ((Nat.log 2 x + 1 : ℕ) : ℝ) ≤ 3 * T := by
    push_cast
    have h₁ := mul_le_mul_of_nonneg_left hlog₂ (show (0 : ℝ) ≤ Nat.log 2 x by positivity)
    change (Nat.log 2 x : ℝ) * Real.log 2 ≤ T at hlog
    linarith
  have hBT : ((Nat.log 2 x + 1 : ℕ) : ℝ) ≤ T ^ 2 := by
    exact hB.trans (by nlinarith)
  have hd := Real.log_le_log (show (0 : ℝ) < ((Nat.log 2 x + 1 : ℕ) : ℝ) by positivity) hBT
  simpa only [Real.log_pow, Nat.cast_ofNat] using hd

/-- Uniform bound for the squared number of cofactor cells on the retained cofactors. -/
theorem eventually_cofactorCellBound_sq_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ m : ℕ, m.primeFactors.card ≤ omegaCutoff x →
      (cofactorCellBound x m : ℝ) ^ 2 ≤ Real.exp (ε * (Real.log (x : ℝ)) ^ (1 / 15 : ℝ)) := by
  have hT : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowT : Tendsto (fun x : ℕ ↦ (Real.log (x : ℝ)) ^ (1 / 15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 15)).comp hT
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 60)).comp_tendsto hT).bound
    (show 0 < ε / 40 by positivity)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hT.eventually (eventually_ge_atTop (3 : ℝ)),
    hpowT.eventually (eventually_ge_atTop (4 * Real.log 6 / ε)), hsmall] with x hx hxlog hlarge hsmallx
  intro m hm
  let T := Real.log (x : ℝ)
  let B : ℕ := Nat.log 2 x + 1
  let D := m.primeFactors.card + 1
  let a : ℝ := T ^ (1 / 20 : ℝ)
  let b : ℝ := T ^ (1 / 15 : ℝ)
  let d : ℝ := T ^ (1 / 60 : ℝ)
  have hT₁ : 3 ≤ T := hxlog
  have hTpos : 0 < T := by linarith
  have hD : (D : ℝ) ≤ a + 1 := by
    have hreal : (m.primeFactors.card : ℝ) ≤ a := by
      exact (Nat.cast_le.mpr hm).trans (Nat.floor_le (Real.rpow_nonneg hTpos.le _))
    simpa [D, Nat.cast_add, Nat.cast_one] using add_le_add_right hreal 1
  have ha : 1 ≤ a := Real.one_le_rpow (by linarith) (by norm_num)
  have hBpos : 0 < (B : ℝ) := by dsimp [B]; positivity
  have hB₁ : 1 ≤ (B : ℝ) := by
    exact_mod_cast (show 1 ≤ B by dsimp [B]; omega)
  have hlogB : Real.log (B : ℝ) ≤ 2 * Real.log T := log_exponent_bound hx hxlog
  have hlogB₀ : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hB₁
  have hlogT₀ : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hd₀ : 0 ≤ d := Real.rpow_nonneg hTpos.le _
  have hsmall' : Real.log T ≤ (ε / 40) * d := by
    change ‖Real.log T‖ ≤ (ε / 40) * ‖d‖ at hsmallx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT₀, abs_of_nonneg hd₀] using hsmallx
  have had : a * d = b := by
    dsimp [a, b, d]
    rw [← Real.rpow_add hTpos]
    norm_num
  have hconst : 2 * Real.log 6 ≤ ε / 2 * b := by
    change 4 * Real.log 6 / ε ≤ b at hlarge
    have hmul := (div_le_iff₀ hε).mp hlarge
    linarith
  have hexp : 2 * (((2 * D + 1 : ℕ) : ℝ)) * Real.log (B : ℝ) ≤ ε / 2 * b := by
    have hk : ((2 * D + 1 : ℕ) : ℝ) ≤ 5 * a := by push_cast; linarith
    calc
      _ ≤ 2 * (5 * a) * (2 * Real.log T) := by gcongr
      _ = 20 * a * Real.log T := by ring
      _ ≤ 20 * a * ((ε / 40) * d) :=
        mul_le_mul_of_nonneg_left hsmall' (by positivity)
      _ = ε / 2 * b := by rw [← had]; ring
  have hsize : (cofactorCellBound x m : ℝ) ≤ 6 * (B : ℝ) ^ (2 * D + 1) := by
    exact_mod_cast (cofactorCellBound_le (m := m) hx)
  calc
    _ ≤ (6 * (B : ℝ) ^ (2 * D + 1)) ^ 2 := by gcongr
    _ = Real.exp (2 * Real.log 6 + 2 * (((2 * D + 1 : ℕ) : ℝ)) * Real.log (B : ℝ)) := by
      calc
        _ = Real.exp (Real.log ((6 * (B : ℝ) ^ (2 * D + 1)) ^ 2)) :=
          (Real.exp_log (by positivity)).symm
        _ = _ := by
          rw [Real.log_pow, Real.log_mul (by norm_num) (pow_ne_zero _ hBpos.ne'), Real.log_pow]
          norm_num
          ring
    _ ≤ _ := Real.exp_le_exp.mpr (by change _ ≤ ε * b; linarith)

end Erdos878
