module

public import Erdos878Proofs.CofactorCount

@[expose] public section

/-! # A lower bound for the equality count -/

namespace Erdos878

open Filter Asymptotics

/-- Prime equality integers give a lower bound of order `x / log x` for `E x`. -/
theorem eventually_x_div_log_le_mul_E :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) / Real.log x ≤ (4 / Real.log 2) * E x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).bound
    (show 0 < Real.log 2 / 4 by positivity)
  filter_upwards [eventually_ge_atTop (3 : ℕ), hlog] with x hx hsmall
  have hxReal : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hxPos : 0 ≤ (x : ℝ) := by positivity
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hsmall' : Real.log (x : ℝ) ≤ Real.log 2 / 4 * x := by
    change ‖Real.log (x : ℝ)‖ ≤ Real.log 2 / 4 * ‖(x : ℝ)‖ at hsmall
    simpa only [Real.norm_of_nonneg hlogx.le, Real.norm_of_nonneg hxPos] using hsmall
  have hprev : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ x by omega), Nat.cast_one]
  have hnext : ((x - 1 : ℕ) : ℝ) + 1 = (x : ℝ) := by rw [hprev]; ring
  have hprevReal : 1 < ((x - 1 : ℕ) : ℝ) := by rw [hprev]; linarith
  have hprevLog : 0 < Real.log ((x - 1 : ℕ) : ℝ) := Real.log_pos hprevReal
  have hlogOrder : Real.log ((x - 1 : ℕ) : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by linarith) (by rw [hprev]; linarith)
  have hnum : (Real.log 2 / 4) * x ≤ ((x - 1 : ℕ) : ℝ) * Real.log 2 - Real.log (x : ℝ) := by
    have hhalf : (x : ℝ) / 2 ≤ (x : ℝ) - 1 := by linarith
    rw [hprev]
    nlinarith [mul_le_mul_of_nonneg_right hhalf hlog2.le]
  have hπ : (((x - 1 : ℕ) : ℝ) * Real.log 2 - Real.log (x : ℝ)) /
      Real.log ((x - 1 : ℕ) : ℝ) ≤ Nat.primeCounting (x - 1) := by
    apply (div_le_iff₀ hprevLog).mpr
    rw [← hnext]
    exact (Chebyshev.psi_ge (x - 1)).trans (Chebyshev.psi_le_primeCounting_mul_log (x - 1))
  have hlower : (Real.log 2 / 4) * (x : ℝ) / Real.log x ≤ (x.primesBelow.card : ℝ) := by
    rw [Nat.primesBelow_card_eq_primeCounting', ← Nat.primeCounting_sub_one]
    calc
      _ ≤ (Real.log 2 / 4) * (x : ℝ) / Real.log ((x - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hprevLog hlogOrder
      _ ≤ _ := (div_le_div_of_nonneg_right hnum hprevLog.le).trans hπ
  have hE := hlower.trans (card_primesBelow_le_E x)
  calc
    _ = (4 / Real.log 2) * ((Real.log 2 / 4) * (x : ℝ) / Real.log x) := by
      field_simp [hlog2.ne', hlogx.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)

theorem x_div_log_isBigO_E :
    (fun x : ℕ ↦ (x : ℝ) / Real.log x) =O[atTop] E := by
  apply IsBigO.of_bound (4 / Real.log 2)
  filter_upwards [eventually_x_div_log_le_mul_E, eventually_ge_atTop (2 : ℕ)] with x h hx
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hE : 0 ≤ E x := by unfold E; positivity
  rwa [Real.norm_of_nonneg (div_nonneg (by positivity) hlog.le), Real.norm_of_nonneg hE]

/-- An absolute error of smaller order than `x / log x` gives an asymptotic
equivalent for the equality count. -/
theorem E_isEquivalent_of_error {G : ℕ → ℝ}
    (h : (fun x ↦ E x - G x) =o[atTop] fun x ↦ (x : ℝ) / Real.log x) :
    E ~[atTop] G := by
  have h' : (fun x ↦ E x - G x) =o[atTop] E := h.trans_isBigO x_div_log_isBigO_E
  have hreverse : (G - E) =o[atTop] E := by
    change (fun x ↦ G x - E x) =o[atTop] E
    simpa only [Pi.neg_apply, neg_sub] using h'.neg_left
  exact hreverse.isEquivalent.symm

end Erdos878
