module

public import Erdos878Proofs.Definitions

@[expose] public section

/-! # Integers with many prime factors or a large square divisor -/

open Filter Asymptotics Finset
open scoped Topology

namespace Erdos878

private lemma pow_primeFactorsCard_le_divisorsCard {n : ℕ} (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  classical
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun t : Finset ℕ ↦ ∏ p ∈ t, p)
  · intro s hs
    change s ∈ _ at hs
    have hsub : s ⊆ n.primeFactors := Finset.mem_powerset.mp hs
    change ∏ p ∈ s, p ∈ n.divisors
    exact Nat.mem_divisors.mpr ⟨(Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans n.prod_primeFactors_dvd, hn.ne'⟩
  · intro s hs t ht he
    change s ∈ _ at hs
    change t ∈ _ at ht
    have hs' : s ⊆ n.primeFactors := Finset.mem_powerset.mp hs
    have ht' : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
    have hmem {s t : Finset ℕ} (hs : s ⊆ n.primeFactors) (ht : t ⊆ n.primeFactors)
        (he : ∏ p ∈ s, p = ∏ p ∈ t, p) : s ⊆ t := by
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors (hs hp)
      have hpd : p ∣ ∏ q ∈ t, q := he ▸ Finset.dvd_prod_of_mem _ hp
      obtain ⟨q, hq, hpq⟩ := (hprime.prime.dvd_finsetProd_iff id).mp hpd
      have : p = q := (Nat.dvd_prime (Nat.prime_of_mem_primeFactors (ht hq))).mp hpq |>.resolve_left hprime.ne_one
      simpa [this] using hq
    exact Finset.Subset.antisymm (hmem hs' ht' he) (hmem ht' hs' he.symm)

private lemma sum_card_divisors (x : ℕ) :
    ∑ n ∈ Icc 1 x, n.divisors.card = ∑ d ∈ Icc 1 x, x / d := by
  classical
  calc
    _ = ∑ n ∈ Icc 1 x, ∑ d ∈ Icc 1 x, if d ∣ n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.card_filter]
      congr 1
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      have hn' := Finset.mem_Icc.mp hn
      constructor
      · rintro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn'.2⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, by omega⟩
    _ = ∑ d ∈ Icc 1 x, ∑ n ∈ Icc 1 x, if d ∣ n then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.card_filter, ← Nat.card_multiples' x d]
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      omega

private lemma divisor_average_le (x : ℕ) :
    (∑ n ∈ Icc 1 x, (n.divisors.card : ℝ)) ≤ (x : ℝ) * (1 + Real.log x) := by
  rw [← Nat.cast_sum, sum_card_divisors, Nat.cast_sum]
  calc
    _ ≤ ∑ d ∈ Icc 1 x, (x : ℝ) / d := by
      apply Finset.sum_le_sum
      intro d _
      exact Nat.cast_div_le
    _ = (x : ℝ) * (harmonic x : ℝ) := by
      simp [harmonic_eq_sum_Icc, div_eq_mul_inv, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by positivity)

private lemma manyPrimeFactors_le (x : ℕ) :
    (manyPrimeFactors x).card * 2 ^ (omegaCutoff x + 1) ≤
      ∑ n ∈ Icc 1 x, n.divisors.card := by
  have hsum : (manyPrimeFactors x).card * 2 ^ (omegaCutoff x + 1) =
      ∑ _n ∈ manyPrimeFactors x, (2 ^ (omegaCutoff x + 1) : ℕ) := by simp
  rw [hsum]
  refine (Finset.sum_le_sum ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ Nat.zero_le _)
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact (Nat.pow_le_pow_right (by decide) hn'.2).trans
      (pow_primeFactorsCard_le_divisorsCard (by have := (Finset.mem_Ico.mp hn'.1).1; omega))
  · intro n hn
    have h := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.le⟩

lemma log_pow_mul_exp_neg_log_rpow_tendsto_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (k : ℕ) :
    Tendsto (fun x : ℕ ↦ Real.log (x : ℝ) ^ k * Real.exp (-c * Real.log (x : ℝ) ^ a)) atTop (𝓝 0) := by
  let L (x : ℕ) := Real.log (x : ℝ)
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) / a) c hc).comp
    ((tendsto_rpow_atTop ha).comp hL)
  refine hh.congr' ?_
  filter_upwards [hL.eventually (eventually_ge_atTop (0 : ℝ))] with x hx
  have ha' : a * ((k : ℝ) / a) = k := by field_simp
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hx, ha', Real.rpow_natCast]

private lemma sum_reciprocal_differences {a b : ℕ} (hab : a ≤ b) :
    ∑ d ∈ Ico a b, ((d : ℝ)⁻¹ - ((d : ℝ) + 1)⁻¹) = (a : ℝ)⁻¹ - (b : ℝ)⁻¹ := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih, Nat.cast_succ]
    ring

private lemma largeSquareDivisor_le (x : ℕ) (hY : 2 ≤ cofactorThreshold x) :
    ((largeSquareDivisor x).card : ℝ) ≤ 2 * (x : ℝ) / cofactorThreshold x := by
  classical
  let D : ℕ := ⌊cofactorThreshold x⌋₊
  let multiples (d : ℕ) := (Finset.range (x + 1)).filter fun n ↦ n ≠ 0 ∧ (d + 1) ^ 2 ∣ n
  have hsubset : largeSquareDivisor x ⊆ (Ico D x).biUnion multiples := by
    intro n hn
    obtain ⟨hn, d, hd, hdy, hdvd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hd₁, hdx⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hn₁, hnx⟩ := Finset.mem_Ico.mp hn
    have hlt : D < d := (Nat.floor_lt (by positivity)).mpr hdy
    refine Finset.mem_biUnion.mpr ⟨d - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by omega,
      (show d - 1 + 1 = d by omega).symm ▸ hdvd⟩
  have hcard : (largeSquareDivisor x).card ≤ ∑ d ∈ Ico D x, x / (d + 1) ^ 2 := by
    simpa [multiples, Nat.card_multiples'] using
      (Finset.card_le_card hsubset).trans (Finset.card_biUnion_le (s := Ico D x) (t := multiples))
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (Nat.one_le_floor_iff _).mpr (by linarith)
  have hYD : cofactorThreshold x ≤ 2 * (D : ℝ) := by
    have := Nat.lt_floor_add_one (cofactorThreshold x)
    change cofactorThreshold x < (D : ℝ) + 1 at this
    linarith
  by_cases hDx : D ≤ x
  · calc
      _ ≤ ∑ d ∈ Ico D x, ((x / (d + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ d ∈ Ico D x, (x : ℝ) * ((d : ℝ)⁻¹ - ((d : ℝ) + 1)⁻¹) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd₀ : 0 < (d : ℝ) := lt_of_lt_of_le (by norm_num) (hD.trans (by exact_mod_cast (Finset.mem_Ico.mp hd).1))
        have hd₁ : 0 < (d : ℝ) + 1 := by positivity
        calc
          _ ≤ (x : ℝ) / ((d : ℝ) + 1) ^ 2 := by
            calc
              _ ≤ (x : ℝ) / (((d + 1) ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
              _ = _ := by push_cast; rfl
          _ ≤ _ := by
            rw [div_eq_mul_inv]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [show (d : ℝ)⁻¹ - ((d : ℝ) + 1)⁻¹ = ((d : ℝ) * ((d : ℝ) + 1))⁻¹ by
              field_simp; ring]
            apply inv_anti₀ (by positivity)
            nlinarith
      _ = (x : ℝ) * ((D : ℝ)⁻¹ - (x : ℝ)⁻¹) := by
        rw [← Finset.mul_sum, sum_reciprocal_differences hDx]
      _ ≤ (x : ℝ) * (D : ℝ)⁻¹ := by gcongr; exact sub_le_self _ (by positivity)
      _ ≤ _ := by
        rw [← div_eq_mul_inv]
        have hY₀ : 0 < cofactorThreshold x := by linarith
        have hD₀ : (0 : ℝ) < D := by linarith
        rw [div_le_div_iff₀ hD₀ hY₀]
        calc
          (x : ℝ) * cofactorThreshold x ≤ (x : ℝ) * (2 * (D : ℝ)) := by gcongr
          _ = _ := by ring
  · have he : (Ico D x) = ∅ := Finset.Ico_eq_empty (by omega)
    simp [he] at hcard
    simpa [hcard] using (show 0 ≤ 2 * (x : ℝ) / cofactorThreshold x by positivity)

/-- Discarding integers divisible by the square of an integer above the cutoff costs `o(x / log x)`. -/
theorem discardLargeSquares_isLittleO :
    (fun x : ℕ ↦ ((largeSquareDivisor x).card : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ) / Real.log x) := by
  apply IsBigO.trans_isLittleO (g := fun x : ℕ ↦ (x : ℝ) / cofactorThreshold x)
  · apply IsBigO.of_bound 2
    have hL : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hY := Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : 0 < (2 / 3 : ℝ))).comp hL)
    filter_upwards [hY.eventually (eventually_ge_atTop (2 : ℝ))] with x hx
    rw [Real.norm_natCast, Real.norm_of_nonneg (by unfold cofactorThreshold; positivity), ← mul_div_assoc]
    exact largeSquareDivisor_le x hx
  · apply isLittleO_of_tendsto' (by
        filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx h
        have hx' : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
        exact (div_ne_zero (lt_trans zero_lt_one hx').ne' (Real.log_pos hx').ne' h).elim)
    have ht := log_pow_mul_exp_neg_log_rpow_tendsto_zero (by norm_num : 0 < (2 / 3 : ℝ)) zero_lt_one 1
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    have hx' : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
    have hx₀ := (lt_trans zero_lt_one hx').ne'
    have hlog := (Real.log_pos hx').ne'
    have he := Real.exp_ne_zero (Real.log (x : ℝ) ^ (2 / 3 : ℝ))
    simp only [pow_one, neg_mul, one_mul, Real.exp_neg, cofactorThreshold]
    field_simp

/-- Discarding integers with too many distinct prime divisors costs `o(x / log x)`. -/
theorem discardManyPrimeFactors_isLittleO :
    (fun x : ℕ ↦ ((manyPrimeFactors x).card : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ) / Real.log x) := by
  apply IsBigO.trans_isLittleO (g := fun x : ℕ ↦
    (x : ℝ) * (1 + Real.log x) * Real.exp (-Real.log 2 * Real.log (x : ℝ) ^ (1 / 20 : ℝ)))
  · apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    have hlog : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx)
    have hb : Real.log (x : ℝ) ^ (1 / 20 : ℝ) ≤ (omegaCutoff x + 1 : ℕ) := by
      simp only [omegaCutoff, Nat.cast_add, Nat.cast_one]
      exact (Nat.lt_floor_add_one _).le
    have hpow : Real.exp (Real.log 2 * Real.log (x : ℝ) ^ (1 / 20 : ℝ)) ≤
        (2 : ℝ) ^ (omegaCutoff x + 1) := by
      calc
        _ ≤ Real.exp (((omegaCutoff x + 1 : ℕ) : ℝ) * Real.log 2) := by
          apply Real.exp_le_exp.mpr
          rw [mul_comm ((omegaCutoff x + 1 : ℕ) : ℝ)]
          gcongr
        _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hmul : ((manyPrimeFactors x).card : ℝ) * (2 : ℝ) ^ (omegaCutoff x + 1) ≤
        ∑ n ∈ Icc 1 x, (n.divisors.card : ℝ) := by exact_mod_cast manyPrimeFactors_le x
    rw [one_mul, Real.norm_natCast, Real.norm_of_nonneg (by positivity), neg_mul,
      Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans (hmul.trans (divisor_average_le x))
  · apply isLittleO_of_tendsto' (by
        filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx h
        have hx' : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
        exact (div_ne_zero (lt_trans zero_lt_one hx').ne' (Real.log_pos hx').ne' h).elim)
    have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h₁ := log_pow_mul_exp_neg_log_rpow_tendsto_zero (by norm_num : 0 < (1 / 20 : ℝ)) hc 1
    have h₂ := log_pow_mul_exp_neg_log_rpow_tendsto_zero (by norm_num : 0 < (1 / 20 : ℝ)) hc 2
    have hh := h₁.add h₂
    rw [add_zero] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    have hx' : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
    have hx₀ := (lt_trans zero_lt_one hx').ne'
    have hlog := (Real.log_pos hx').ne'
    simp only [pow_one]
    field_simp

end Erdos878
