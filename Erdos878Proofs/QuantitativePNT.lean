module

public import Erdos878Proofs.Definitions
public import PrimeNumberTheoremAnd.Consequences
public import PrimeNumberTheoremAnd.MediumPNT

@[expose] public section

/-!
# Quantitative prime counting for Erdős problem 878(iv)

We transfer the quantitative estimate for Chebyshev's psi function to the
prime-counting function by Abel summation. The integral is split at the
square root of its upper endpoint.
-/

open Filter Asymptotics MeasureTheory Real
open scoped Chebyshev Interval

noncomputable section

namespace Erdos878

private def decay (c x : ℝ) : ℝ := exp (-c * log x ^ (1 / 10 : ℝ))

private theorem decay_pos (c x : ℝ) : 0 < decay c x := exp_pos _

private theorem exp_log_half_eq_sqrt {x : ℝ} (hx : 0 < x) :
    exp (log x / 2) = √x := by rw [← log_sqrt hx.le, exp_log (sqrt_pos.2 hx)]

private theorem sqrt_le_decay_eventually {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x * decay c x ∧
      √x ≤ x * decay c x ∧ √x * log x ≤ 4 * (x * decay c x) := by
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (max 1 ((4 * c) ^ 2))
  filter_upwards [hlog, eventually_gt_atTop 0] with x hL hx
  have hL1 : 1 ≤ log x := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ log x := zero_le_one.trans hL1
  have hs : 4 * c ≤ √(log x) := le_sqrt_of_sq_le ((le_max_right _ _).trans hL)
  have hcL : c * log x ^ (1 / 10 : ℝ) ≤ log x / 4 := by
    have hpow : log x ^ (1 / 10 : ℝ) ≤ √(log x) := by
      rw [sqrt_eq_rpow]
      exact rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    calc
      _ ≤ c * √(log x) := mul_le_mul_of_nonneg_left hpow hc.le
      _ = (4 * c * √(log x)) / 4 := by ring
      _ ≤ (√(log x) * √(log x)) / 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs (sqrt_nonneg _)) (by norm_num)
      _ = _ := by rw [mul_self_sqrt hL0]
  have hE : exp (3 * log x / 4) ≤ x * decay c x := by
    calc
      _ ≤ exp (log x + (-c * log x ^ (1 / 10 : ℝ))) := by
        apply exp_le_exp.mpr
        linarith
      _ = _ := by rw [exp_add, exp_log hx]; rfl
  have h1 : 1 ≤ exp (3 * log x / 4) := one_le_exp_iff.mpr (by positivity)
  have h2 : √x ≤ exp (3 * log x / 4) := by
    rw [← exp_log_half_eq_sqrt hx]
    exact exp_le_exp.mpr (by linarith)
  have h3 : √x * log x ≤ 4 * exp (3 * log x / 4) := by
    have hh : log x ≤ 4 * exp (log x / 4) := by linarith [add_one_le_exp (log x / 4)]
    calc
      _ ≤ √x * (4 * exp (log x / 4)) := mul_le_mul_of_nonneg_left hh (sqrt_nonneg _)
      _ = _ := by
        rw [← exp_log_half_eq_sqrt hx, show 3 * log x / 4 = log x / 2 + log x / 4 by ring,
          exp_add]
        ring
  exact ⟨h1.trans hE, h2.trans hE, h3.trans (mul_le_mul_of_nonneg_left hE (by norm_num))⟩

private theorem quantitative_theta :
    ∃ c > 0, (fun x : ℝ ↦ θ x - x) =O[atTop] fun x ↦ x * decay c x := by
  obtain ⟨c, hc, hpsi⟩ := MediumPNT
  obtain ⟨B, hB, hbound⟩ := hpsi.exists_pos
  refine ⟨c, hc, IsBigO.of_bound (B + 8) ?_⟩
  filter_upwards [hbound.bound, sqrt_le_decay_eventually hc, eventually_ge_atTop 2]
    with x hpsi hsmall hx
  have hright : 0 ≤ x * decay c x := by linarith [hsmall.1]
  have hp : ‖ψ x - x‖ ≤ B * (x * decay c x) := by
    change ‖ψ x - x‖ ≤ B * ‖x * decay c x‖ at hpsi
    simpa only [Real.norm_of_nonneg hright] using hpsi
  have hpt : ‖ψ x - θ x‖ ≤ 2 * (√x * log x) := by
    simpa only [Real.norm_eq_abs, mul_assoc] using
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)
  rw [Real.norm_of_nonneg hright]
  calc
    _ = ‖(ψ x - x) - (ψ x - θ x)‖ := by congr 1; ring
    _ ≤ ‖ψ x - x‖ + ‖ψ x - θ x‖ := norm_sub_le _ _
    _ ≤ B * (x * decay c x) + 2 * (√x * log x) := add_le_add hp hpt
    _ ≤ _ := by linarith [hsmall.2.2]

private theorem decay_mono {c a b : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ a) (hab : a ≤ b) :
    decay c b ≤ decay c a := by
  have hlog := Real.log_le_log (zero_lt_one.trans_le ha) hab
  have hpow := rpow_le_rpow (log_nonneg ha) hlog (by norm_num : (0 : ℝ) ≤ 1 / 10)
  exact exp_le_exp.mpr (by nlinarith)

private theorem decay_sqrt_le {c x : ℝ} (hc : 0 ≤ c) (hx : 1 ≤ x) :
    decay c (√x) ≤ decay (c / 2) x := by
  have hz := log_nonneg hx
  have hr : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 10 : ℝ) := by
    simpa using rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (by norm_num : (1 / 10 : ℝ) ≤ 1)
  have hlog : (1 / 2) * log x ^ (1 / 10 : ℝ) ≤ log (√x) ^ (1 / 10 : ℝ) := by
    rw [log_sqrt (zero_le_one.trans hx),
      show log x / 2 = (1 / 2) * log x by ring,
      mul_rpow (show (0 : ℝ) ≤ 1 / 2 by norm_num) hz]
    exact mul_le_mul_of_nonneg_right hr (rpow_nonneg hz _)
  unfold decay
  apply exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlog hc
  linarith

private def err (t : ℝ) : ℝ := (θ t - t) / (t * log t ^ 2)

private theorem θ_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ θ t / (t * log t ^ 2)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set
  exact Set.Icc_subset_Icc_left ha

private theorem lin_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ t / (t * log t ^ 2)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  have ht' : 2 ≤ t := ha.trans ht.1
  have ht0 : 0 < t := by linarith
  have hlog : 0 < log t := log_pos (by linarith)
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))

private theorem err_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable err volume a b := by
  change IntervalIntegrable (fun t ↦ (θ t - t) / (t * log t ^ 2)) volume a b
  simpa only [sub_div, Pi.sub_apply] using
    (θ_intervalIntegrable ha hab).sub (lin_intervalIntegrable ha hab)

private theorem primeCounting_sub_li {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in 2..x, (log t)⁻¹ =
      (θ x - x) / log x + (∫ t in 2..x, err t) + 2 / log 2 := by
  have h := integral_log_inv 2 x (by norm_num) hx
  have hint :
      (∫ t in 2..x, t / (t * log t ^ 2)) = ∫ t in 2..x, (log t ^ 2)⁻¹ := by
    refine intervalIntegral.integral_congr (fun t ht ↦ ?_)
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have htlog : 0 < log t := log_pos (by linarith [ht.1])
    field_simp
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx, h]
  unfold err
  simp_rw [sub_div]
  rw [intervalIntegral.integral_sub (θ_intervalIntegrable (le_refl _) hx)
    (lin_intervalIntegrable (le_refl _) hx), hint]
  ring

private theorem err_norm_integral_le {a b d : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hd : 0 ≤ d)
    (h : ∀ t ∈ Set.Icc a b, ‖θ t - t‖ ≤ t * d) :
    ‖∫ t in a..b, err t‖ ≤ (d / log 2 ^ 2) * (b - a) := by
  rw [← abs_of_nonneg (sub_nonneg.mpr hab)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [Set.uIoc_of_le hab] at ht
  have htt : 2 ≤ t := ha.trans ht.1.le
  have ht0 : 0 < t := by linarith
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog : log 2 ≤ log t := log_le_log (by norm_num) htt
  have hs : log 2 ^ 2 ≤ log t ^ 2 := by nlinarith
  have hlogt : 0 < log t := hlog2.trans_le hlog
  have hdpos : 0 < t * log t ^ 2 := by positivity
  rw [err, norm_div, Real.norm_of_nonneg hdpos.le]
  calc
    _ ≤ (t * d) / (t * log t ^ 2) :=
      div_le_div_of_nonneg_right (h t ⟨ht.1.le, ht.2⟩) hdpos.le
    _ = d / log t ^ 2 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left hd (by positivity) hs

private theorem theta_crude {t : ℝ} (ht : 0 ≤ t) :
    ‖θ t - t‖ ≤ t * (1 + log 4) := by
  calc
    _ ≤ ‖θ t‖ + ‖t‖ := norm_sub_le _ _
    _ = θ t + t := by rw [Real.norm_of_nonneg (Chebyshev.theta_nonneg _), Real.norm_of_nonneg ht]
    _ ≤ _ := by linarith [Chebyshev.theta_le_log4_mul_x ht]

/-- Quantitative prime number theorem for the logarithmic integral starting at two. -/
theorem primeCounting_sub_li_isBigO :
    ∃ c > 0, (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ u in 2..x, (log u)⁻¹)
      =O[atTop] fun x ↦ x * exp (-c * (log x) ^ (1 / 10 : ℝ)) := by
  obtain ⟨c, hc, htheta⟩ := quantitative_theta
  obtain ⟨B, hB, htheta⟩ := htheta.exists_pos
  obtain ⟨a, ha⟩ := eventually_atTop.1 htheta.bound
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  let C₁ := B / log 2
  let C₂ := (1 + log 4) / log 2 ^ 2
  let C₃ := B / log 2 ^ 2
  let C₄ := 2 / log 2
  refine ⟨c / 2, by positivity, IsBigO.of_bound (C₁ + C₂ + C₃ + C₄) ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 (a ^ 2)), sqrt_le_decay_eventually (show 0 < c / 2 by positivity)]
    with x hx hsmall
  have hx4 := (le_max_left _ _).trans hx
  have hxa := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hs2 : 2 ≤ √x := le_sqrt_of_sq_le (by norm_num; exact hx4)
  have hsa : a ≤ √x := le_sqrt_of_sq_le hxa
  have hsx : √x ≤ x := sqrt_le_self_iff.mpr (Or.inr (by linarith))
  let Z := x * decay (c / 2) x
  have hZ : 0 ≤ Z := mul_nonneg hx0.le (decay_pos _ _).le
  have hZ1 : 1 ≤ Z := hsmall.1
  have hnorm (t : ℝ) (hts : √x ≤ t) : ‖θ t - t‖ ≤ B * (t * decay (c / 2) x) := by
    have ht0 : 0 ≤ t := (sqrt_nonneg _).trans hts
    have hta := hsa.trans hts
    have hc' : 0 ≤ c := hc.le
    have hmono := decay_mono hc' ((by norm_num : (1 : ℝ) ≤ 2).trans hs2) hts
    have hdec := hmono.trans (decay_sqrt_le hc' (by linarith : 1 ≤ x))
    calc
      _ ≤ B * (t * decay c t) := by
        simpa [Real.norm_of_nonneg (mul_nonneg ht0 (decay_pos _ _).le)] using ha t hta
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdec ht0) hB.le
  have hterm₁ : ‖(θ x - x) / log x‖ ≤ C₁ * Z := by
    have hlogx : 0 < log x := log_pos (by linarith)
    rw [norm_div, Real.norm_of_nonneg hlogx.le]
    calc
      _ ≤ (B * Z) / log x := div_le_div_of_nonneg_right (hnorm x hsx) hlogx.le
      _ ≤ (B * Z) / log 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hB.le hZ) hlog2 (log_le_log (by norm_num) hx2)
      _ = _ := by dsimp [C₁]; ring
  have hterm₂ : ‖∫ t in 2..√x, err t‖ ≤ C₂ * Z := by
    have hh := err_norm_integral_le (le_refl _) hs2
      (show 0 ≤ 1 + log 4 by positivity)
      (fun t ht ↦ theta_crude (by linarith [ht.1]))
    have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hsmall.2.1]) hC₂)
  have hterm₃ : ‖∫ t in √x..x, err t‖ ≤ C₃ * Z := by
    have hh := err_norm_integral_le hs2 hsx
      (show 0 ≤ B * decay (c / 2) x from mul_nonneg hB.le (decay_pos _ _).le)
      (fun t ht ↦ by simpa only [mul_assoc, mul_left_comm] using hnorm t ht.1)
    have hC : 0 ≤ B * decay (c / 2) x / log 2 ^ 2 := by
      have := decay_pos (c / 2) x
      positivity
    calc
      _ ≤ (B * decay (c / 2) x / log 2 ^ 2) * (x - √x) := hh
      _ ≤ (B * decay (c / 2) x / log 2 ^ 2) * x :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (sqrt_nonneg _)) hC
      _ = _ := by dsimp [C₃, Z]; ring
  have hterm₄ : ‖2 / log 2‖ ≤ C₄ * Z := by
    rw [show (2 : ℝ) / log 2 = C₄ by rfl, Real.norm_of_nonneg (by dsimp [C₄]; positivity)]
    exact le_mul_of_one_le_right (by dsimp [C₄]; positivity) hZ1
  change ‖(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ u in 2..x, (log u)⁻¹‖ ≤
    (C₁ + C₂ + C₃ + C₄) * ‖Z‖
  rw [primeCounting_sub_li hx2, Real.norm_of_nonneg hZ,
    ← intervalIntegral.integral_add_adjacent_intervals
      (err_intervalIntegrable (le_refl _) hs2) (err_intervalIntegrable hs2 hsx)]
  calc
    _ ≤ ‖(θ x - x) / log x‖ + (‖∫ t in 2..√x, err t‖ + ‖∫ t in √x..x, err t‖) + ‖2 / log 2‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) le_rfl)
    _ ≤ _ := by nlinarith

#print axioms primeCounting_sub_li_isBigO

end Erdos878
