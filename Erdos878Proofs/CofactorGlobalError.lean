module

public import Erdos878Proofs.CofactorApproximation
public import Erdos878Proofs.CofactorCount
public import Erdos878Proofs.CofactorGrowth
public import Erdos878Proofs.DiscardArithmetic

@[expose] public section

/-! # Summing the cofactor approximation over the retained indices -/

open Filter Asymptotics
open scoped Topology

namespace Erdos878

/-- The finite sum of logarithmic integrals in the answer to part (iv). -/
noncomputable def cofactorAnswer (x : ℕ) : ℝ :=
  ∑ m ∈ cofactorIndices x (omegaCutoff x) (cofactorThreshold x),
    cofactorIntegral x m (cofactorLower m (cofactorThreshold x)) (cofactorUpper x m)

/-- The prime counts represented by these integrals. -/
noncomputable def cofactorPrimeSum (x : ℕ) : ℝ :=
  ∑ m ∈ cofactorIndices x (omegaCutoff x) (cofactorThreshold x),
    ((cofactorPrimes x m (cofactorThreshold x)).card : ℝ)

private lemma harmonic_cofactorIndices_le (x K : ℕ) (Y : ℝ) :
    (∑ m ∈ cofactorIndices x K Y, (m : ℝ)⁻¹) ≤ 1 + Real.log x := by
  have hset : cofactorIndices x K Y ⊆ Finset.Icc 1 x := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1,
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).2.le⟩
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 x, (m : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hset (fun m _ _ ↦ by positivity)
    _ = (harmonic x : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log x

private lemma event_cofactor_error_bound :
    ∃ d > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      |cofactorPrimeSum x - cofactorAnswer x| ≤ C * (x : ℝ) * (1 + Real.log x) *
        Real.exp (-d * (Real.log (x : ℝ)) ^ (1 / 15 : ℝ)) := by
  obtain ⟨c, hc, C, hC, A, hA, hap⟩ := cofactorApproximation
  let d : ℝ := min c 1
  have hd : 0 < d := lt_min hc zero_lt_one
  have hd₁ : d ≤ 1 := min_le_right _ _
  have hdc : d ≤ c := min_le_left _ _
  refine ⟨d / 2, by positivity, 2 * C, by positivity, ?_⟩
  have hT : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hY : Tendsto cofactorThreshold atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hT)
  filter_upwards [hT.eventually (eventually_ge_atTop (1 : ℝ)),
    hY.eventually (eventually_ge_atTop A), eventually_cofactorCellBound_sq_le_exp (show 0 < d / 2 by positivity)]
    with x hx hYx hB
  let Y : ℝ := cofactorThreshold x
  let T : ℝ := Real.log (x : ℝ)
  let L : ℝ := T ^ (1 / 15 : ℝ)
  have hT₁ : 1 ≤ T := hx
  have hYpos : 0 < Y := Real.exp_pos _
  have hL₀ : 0 ≤ L := Real.rpow_nonneg (zero_le_one.trans hT₁) _
  have hlogY : Real.log Y = T ^ (2 / 3 : ℝ) := by simp [Y, T, cofactorThreshold]
  have hlogY₀ : 0 ≤ Real.log Y := by rw [hlogY]; exact Real.rpow_nonneg (zero_le_one.trans hT₁) _
  have hlogYpow : (Real.log Y) ^ (1 / 10 : ℝ) = L := by
    rw [hlogY, ← Real.rpow_mul (zero_le_one.trans hT₁)]
    norm_num [L]
  have hed : Real.exp (d * L) ≤ Y := by
    rw [show Y = Real.exp (T ^ (2 / 3 : ℝ)) from rfl]
    apply Real.exp_le_exp.mpr
    calc
      d * L ≤ 1 * L := mul_le_mul_of_nonneg_right hd₁ hL₀
      _ = L := one_mul _
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT₁ (by norm_num)
  have hsingle (m : ℕ) (hm : m ∈ cofactorIndices x (omegaCutoff x) Y) :
      |((cofactorPrimes x m Y).card : ℝ) -
        cofactorIntegral x m (cofactorLower m Y) (cofactorUpper x m)| ≤
          (2 * C) * ((x : ℝ) / m) * Real.exp (-(d / 2) * L) := by
    let l : ℝ := cofactorLower m Y
    let r : ℝ := cofactorUpper x m
    have hl : Y ≤ l := le_max_left _ _
    have hm' := (Finset.mem_filter.mp hm).2
    have hr : Y < r := hm'.2
    have hr0 : 0 < r := hYpos.trans hr
    change _ ≤ (2 * C) * r * Real.exp (-(d / 2) * L)
    have hm0 : 0 < m := (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1
    rw [cofactorPrimes_eq_goodIntervalPrimes x m Y hm0]
    by_cases hlr : l < r
    · have hlogL : L ≤ (Real.log l) ^ (1 / 10 : ℝ) := by
        rw [← hlogYpow]
        exact Real.rpow_le_rpow hlogY₀ (Real.log_le_log hYpos hl) (by norm_num)
      have he : Real.exp (-c * (Real.log l) ^ (1 / 10 : ℝ)) ≤ Real.exp (-d * L) := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ -c * L := mul_le_mul_of_nonpos_left hlogL (neg_nonpos.mpr hc.le)
          _ ≤ _ := mul_le_mul_of_nonneg_right (neg_le_neg hdc) hL₀
      have h1 : 1 ≤ r * Real.exp (-d * L) := by
        calc
          1 = Real.exp (d * L) * Real.exp (-d * L) := by rw [← Real.exp_add]; simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (hed.trans hr.le) (Real.exp_pos _).le
      have hZ : r * Real.exp (-c * (Real.log l) ^ (1 / 10 : ℝ)) + 1 ≤
          2 * r * Real.exp (-d * L) := by
        have h₀ := mul_le_mul_of_nonneg_left he hr0.le
        linarith
      have hA' : A ≤ l := hYx.trans hl
      calc
        _ ≤ C * (r * Real.exp (-c * (Real.log l) ^ (1 / 10 : ℝ)) + 1) *
            (cofactorCellBound x m : ℝ) ^ 2 := hap x m l r hA' hlr
        _ ≤ C * (2 * r * Real.exp (-d * L)) * Real.exp ((d / 2) * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hZ hC.le) (hB m hm'.1)
            (sq_nonneg _) (by positivity)
        _ = _ := by
          rw [show C * (2 * r * Real.exp (-d * L)) * Real.exp (d / 2 * L) =
            (2 * C) * r * (Real.exp (-d * L) * Real.exp (d / 2 * L)) by ring,
            ← Real.exp_add, show -d * L + d / 2 * L = -(d / 2) * L by ring]
    · rw [goodIntervalPrimes_eq_empty_of_ge (le_of_not_gt hlr),
        cofactorIntegral_eq_zero_of_ge (le_of_not_gt hlr)]
      simp only [Finset.card_empty, Nat.cast_zero, sub_zero, abs_zero]
      positivity
  let S := cofactorIndices x (omegaCutoff x) Y
  let R : ℝ := Real.exp (-(d / 2) * L)
  unfold cofactorPrimeSum cofactorAnswer
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ m ∈ S, (2 * C) * ((x : ℝ) / m) * R := Finset.sum_le_sum hsingle
    _ = (2 * C) * (x : ℝ) * (∑ m ∈ S, (m : ℝ)⁻¹) * R := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [div_eq_mul_inv]
      ring
    _ ≤ _ := by
      change (2 * C) * (x : ℝ) * (∑ m ∈ S, (m : ℝ)⁻¹) * R ≤
        (2 * C) * (x : ℝ) * (1 + Real.log x) * R
      gcongr
      exact harmonic_cofactorIndices_le x (omegaCutoff x) Y

/-- Replacing all the cofactor prime counts by integrals costs `o(x / log x)`. -/
theorem cofactor_primes_sub_answer_isLittleO :
    (cofactorPrimeSum - cofactorAnswer) =o[atTop] (fun x : ℕ ↦ (x : ℝ) / Real.log x) := by
  obtain ⟨d, hd, C, _, h⟩ := event_cofactor_error_bound
  have h₁ := log_pow_mul_exp_neg_log_rpow_tendsto_zero (by norm_num : 0 < (1 / 15 : ℝ)) hd 1
  have h₂ := log_pow_mul_exp_neg_log_rpow_tendsto_zero (by norm_num : 0 < (1 / 15 : ℝ)) hd 2
  have hlim : Tendsto (fun x : ℕ ↦ C * (Real.log (x : ℝ) *
        Real.exp (-d * Real.log (x : ℝ) ^ (1 / 15 : ℝ)) +
      Real.log (x : ℝ) ^ 2 * Real.exp (-d * Real.log (x : ℝ) ^ (1 / 15 : ℝ)))) atTop (𝓝 0) := by
    simpa using (h₁.add h₂).const_mul C
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    have hx' : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
    exact fun h' ↦ False.elim ((div_pos (zero_lt_one.trans hx') (Real.log_pos hx')).ne' h')
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with x hx hx2
    have hx' : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
    have hx0 : 0 < (x : ℝ) := zero_lt_one.trans hx'
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hx'
    have hden : 0 < (x : ℝ) / Real.log x := div_pos hx0 hlog
    simp only [Pi.sub_apply, Real.norm_eq_abs, abs_div, abs_of_pos hden]
    refine (div_le_div_of_nonneg_right hx hden.le).trans_eq ?_
    field_simp

end Erdos878
