module

public import Erdos878Proofs.Definitions
public import PrimeNumberTheoremAnd.IEANTN.Mertens

@[expose] public section

/-! # The smooth-number exception in Erdős Problem 878(iv) -/

open Filter Asymptotics
open scoped Topology

namespace Erdos878

/-- The smooth-number threshold, with naturals at the real threshold included. -/
noncomputable def smoothCutoff (x : ℕ) : ℕ := ⌊cofactorThreshold x⌋₊ + 1

private noncomputable def rankinWeight (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' n m := by
    push_cast
    exact Real.mul_rpow (by positivity) (by positivity)

private lemma rankin_count {s : ℝ} (hs : 0 < s) (x k : ℕ) :
    ((x.smoothNumbersUpTo k).card : ℝ) ≤
      (x : ℝ) ^ s * ∏ p ∈ k.primesBelow, (1 - (p : ℝ) ^ (-s))⁻¹ := by
  classical
  let a : Finset k.smoothNumbers := (x.smoothNumbersUpTo k).subtype (· ∈ k.smoothNumbers)
  have hcard : a.card = (x.smoothNumbersUpTo k).card := by
    unfold a
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    exact fun n hn ↦ (Nat.mem_smoothNumbersUpTo.mp hn).2
  have h := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rankinWeight s) (fun {p} hp ↦ by
      have hp' : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      change ‖(p : ℝ) ^ (-s)‖ < 1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp' (neg_neg_of_pos hs)) k
  have hf : ∀ n : k.smoothNumbers, 0 ≤ rankinWeight s n :=
    fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsum : Summable (fun n : k.smoothNumbers ↦ rankinWeight s n) := h.2.summable
  have hfinite : (∑ n ∈ a, rankinWeight s n) ≤ ∑' n : k.smoothNumbers, rankinWeight s n :=
    hsum.sum_le_tsum a (fun n _ ↦ hf n)
  calc
    _ = ∑ _n ∈ a, (1 : ℝ) := by simp [hcard]
    _ ≤ ∑ n ∈ a, (x : ℝ) ^ s * rankinWeight s n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Nat.mem_smoothNumbersUpTo.mp (Finset.mem_subtype.mp hn)
      have hnx : ((n : ℕ) : ℝ) ≤ x := by exact_mod_cast hn'.1
      have hpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
      have hpow : ((n : ℕ) : ℝ) ^ s ≤ (x : ℝ) ^ s := Real.rpow_le_rpow hpos.le hnx hs.le
      change 1 ≤ (x : ℝ) ^ s * ((n : ℕ) : ℝ) ^ (-s)
      rw [Real.rpow_neg hpos.le]
      exact (mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos s).ne').ge.trans
        (mul_le_mul_of_nonneg_right hpow (by positivity))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hfinite.trans_eq h.2.tsum_eq) (by positivity)

private lemma inverse_factor_le_exp {t q : ℝ} (ht : 0 ≤ t) (hqt : t ≤ q) (hq : q < 1) :
    (1 - t)⁻¹ ≤ Real.exp ((1 - q)⁻¹ * t) := by
  have ht1 : 0 < 1 - t := sub_pos.mpr (hqt.trans_lt hq)
  have hq1 : 0 < 1 - q := sub_pos.mpr hq
  have hinv : (1 - t)⁻¹ ≤ (1 - q)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hq1 (by linarith : 1 - q ≤ 1 - t)
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr ht1)
  have heq : (1 - t)⁻¹ - 1 = t * (1 - t)⁻¹ := by
    field_simp
    ring
  rw [heq] at hlog
  have hlast := hlog.trans (mul_le_mul_of_nonneg_left hinv ht)
  simpa only [Real.exp_log (inv_pos.mpr ht1), mul_comm t] using Real.exp_le_exp.mpr hlast

private lemma smooth_euler_product_bound {y : ℝ} (hy : 2 ≤ y) (hylog : 2 ≤ Real.log y) :
    let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
    let s : ℝ := 1 - 1 / Real.log y
    (∏ p ∈ (⌊y⌋₊ + 1).primesBelow, (1 - (p : ℝ) ^ (-s))⁻¹) ≤
      Real.exp ((1 - q)⁻¹ * Real.exp 1 *
        (∑ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, 1 / (p : ℝ))) := by
  dsimp only
  let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  let s : ℝ := 1 - 1 / Real.log y
  change (∏ p ∈ (⌊y⌋₊ + 1).primesBelow, (1 - (p : ℝ) ^ (-s))⁻¹) ≤ _
  have hq : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hs : (1 / 2 : ℝ) ≤ s := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hylog
    dsimp [s]
    linarith
  have hylogpos : 0 < Real.log y := by linarith
  have hprod (p : ℕ) (hp : p ∈ (⌊y⌋₊ + 1).primesBelow) :
      (1 - (p : ℝ) ^ (-s))⁻¹ ≤ Real.exp ((1 - q)⁻¹ * Real.exp 1 * (1 / (p : ℝ))) := by
    have hpr := Nat.mem_primesBelow.mp hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.2.two_le
    have hp0 : 0 < (p : ℝ) := by linarith
    have hpx : (p : ℝ) ≤ y := by
      exact (show (p : ℝ) ≤ (⌊y⌋₊ : ℝ) by exact_mod_cast Nat.lt_succ_iff.mp hpr.1).trans
        (Nat.floor_le (by linarith))
    have ht : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg hp0.le _
    have htq : (p : ℝ) ^ (-s) ≤ q := by
      calc
        _ ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    have hte : (p : ℝ) ^ (-s) ≤ Real.exp 1 * (1 / (p : ℝ)) := by
      have he : -s = -1 + 1 / Real.log y := by dsimp [s]; ring
      have harg : Real.log p * (1 / Real.log y) ≤ 1 := by
        rw [show Real.log p * (1 / Real.log y) = Real.log p / Real.log y by ring]
        exact (div_le_one₀ hylogpos).mpr (Real.log_le_log hp0 hpx)
      rw [he, Real.rpow_add hp0, Real.rpow_neg_one, Real.rpow_def_of_pos hp0, mul_comm (Real.exp 1)]
      simpa only [one_div] using
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (inv_nonneg.mpr hp0.le)
    refine (inverse_factor_le_exp ht htq hq).trans (Real.exp_le_exp.mpr ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hte (inv_nonneg.mpr (sub_nonneg.mpr hq.le))
  have heq : (⌊y⌋₊ + 1).primesBelow = (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc, Nat.lt_succ_iff]
    exact ⟨fun h ↦ ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h ↦ ⟨h.1.2, h.2⟩⟩
  calc
    _ ≤ ∏ p ∈ (⌊y⌋₊ + 1).primesBelow, Real.exp ((1 - q)⁻¹ * Real.exp 1 * (1 / (p : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hpr := (Nat.mem_primesBelow.mp hp).2
        have hp' : 1 < (p : ℝ) := by exact_mod_cast hpr.one_lt
        have ht := Real.rpow_lt_one_of_one_lt_of_neg (z := -s) hp' (by linarith)
        exact inv_nonneg.mpr (sub_nonneg.mpr ht.le)
      · exact hprod
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum, heq]

private noncomputable def smoothRoot (x : ℕ) : ℝ := (Real.log (x : ℝ)) ^ (1 / 3 : ℝ)

private lemma smoothRoot_tendsto : Tendsto smoothRoot atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The count discarded because every prime factor is below the cofactor threshold. -/
theorem discardSmooth_isLittleO :
    (fun x : ℕ ↦ ((x.smoothNumbersUpTo (smoothCutoff x)).card : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log x) := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  let D : ℝ := (1 - q)⁻¹ * Real.exp 1
  let A : ℝ := 2 * D + 3
  have hq : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hD : 0 < D := mul_pos (inv_pos.mpr (sub_pos.mpr hq)) (Real.exp_pos _)
  have hA : 0 < A := by dsimp [A]; linarith
  have htail : Tendsto (fun x : ℕ ↦ Real.exp (-(smoothRoot x) / 2 + D * C)) atTop (𝓝 0) := by
    have hn := tendsto_neg_atTop_atBot.comp (smoothRoot_tendsto.atTop_div_const (by norm_num : 0 < (2 : ℝ)))
    have ht : Tendsto (fun x : ℕ ↦ Real.exp (-(smoothRoot x) / 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (by simpa only [Function.comp_def, neg_div] using hn)
    simpa [Real.exp_add] using ht.mul_const (Real.exp (D * C))
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto smoothRoot_tendsto).bound
    (show 0 < 1 / (2 * A) by positivity)
  have hmajor : ∀ᶠ x : ℕ in atTop,
      ((x.smoothNumbersUpTo (smoothCutoff x)).card : ℝ) / ((x : ℝ) / Real.log x) ≤
        Real.exp (-(smoothRoot x) / 2 + D * C) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      smoothRoot_tendsto.eventually (eventually_ge_atTop (2 : ℝ)), hsmall] with x hx hu hsmallx
    let u : ℝ := smoothRoot x
    let y : ℝ := cofactorThreshold x
    let s : ℝ := 1 - 1 / Real.log y
    have hx' : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
    have hxpos : 0 < (x : ℝ) := zero_lt_one.trans hx'
    have hlogx := Real.log_pos hx'
    have hu' : 2 ≤ u := hu
    have hupos : 0 < u := by linarith
    have hcub : u ^ 3 = Real.log x := by
      dsimp [u, smoothRoot]
      rw [← Real.rpow_mul_natCast hlogx.le]
      norm_num
    have hlogy : Real.log y = u ^ 2 := by
      dsimp [y, cofactorThreshold, u, smoothRoot]
      rw [Real.log_exp, ← Real.rpow_mul_natCast hlogx.le]
      norm_num
    have hylog : 2 ≤ Real.log y := by rw [hlogy]; nlinarith
    have hy : 2 ≤ y := by
      have hyle := Real.add_one_le_exp (Real.log y)
      have hypos : 0 < y := by dsimp [y, cofactorThreshold]; positivity
      rw [Real.exp_log hypos] at hyle
      linarith
    have hs : 0 < s := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hylog
      dsimp [s]
      linarith
    have hcount : ((x.smoothNumbersUpTo (smoothCutoff x)).card : ℝ) ≤
        (x : ℝ) ^ s * Real.exp (D * (Real.log (Real.log y) + C)) := by
      have hm := (abs_le.mp (hC y hy)).2
      have hupp : (∑ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, 1 / (p : ℝ)) ≤
          Real.log (Real.log y) + C := by linarith
      exact (rankin_count hs x (smoothCutoff x)).trans (mul_le_mul_of_nonneg_left
        ((smooth_euler_product_bound hy hylog).trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hupp hD.le))) (Real.rpow_nonneg hxpos.le _))
    have hpow : (x : ℝ) ^ s / x = Real.exp (-u) := by
      calc
        _ = Real.exp (Real.log x * s) / Real.exp (Real.log x) := by
          rw [Real.rpow_def_of_pos hxpos, Real.exp_log hxpos]
        _ = Real.exp (Real.log x * s - Real.log x) := (Real.exp_sub _ _).symm
        _ = _ := by
          congr 1
          dsimp [s]
          rw [← hcub, hlogy]
          field_simp
          ring
    have hloglog : Real.log (Real.log y) = 2 * Real.log u := by
      rw [hlogy, Real.log_pow]
      norm_num
    have hlogexp : Real.log x = Real.exp (3 * Real.log u) := by
      rw [← hcub, ← Real.exp_log (pow_pos hupos 3), Real.log_pow]
      norm_num
    have hlogsmall : A * Real.log u ≤ u / 2 := by
      have hs' : Real.log u ≤ (1 / (2 * A)) * u := by
        change ‖Real.log u‖ ≤ (1 / (2 * A)) * ‖u‖ at hsmallx
        simpa only [Real.norm_eq_abs, abs_of_nonneg hupos.le,
          abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ u))] using hsmallx
      calc
        _ ≤ A * ((1 / (2 * A)) * u) := mul_le_mul_of_nonneg_left hs' hA.le
        _ = _ := by field_simp
    calc
      _ ≤ ((x : ℝ) ^ s * Real.exp (D * (Real.log (Real.log y) + C))) /
          ((x : ℝ) / Real.log x) :=
        div_le_div_of_nonneg_right hcount (div_nonneg hxpos.le hlogx.le)
      _ = ((x : ℝ) ^ s / x) * Real.exp (D * (Real.log (Real.log y) + C)) * Real.log x := by
        field_simp
      _ = Real.exp (A * Real.log u - u + D * C) := by
        rw [hpow, hloglog, hlogexp, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp only [A]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    have hx' : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
    exact fun h ↦ False.elim ((div_pos (zero_lt_one.trans hx') (Real.log_pos hx')).ne' h)
  · exact squeeze_zero' (Eventually.of_forall fun x ↦ by
      exact div_nonneg (by positivity) (div_nonneg (by positivity) (Real.log_natCast_nonneg _)))
      hmajor htail

end Erdos878
