module

public import Erdos878Proofs.CofactorCount
public import Erdos878Proofs.QuantitativePNT

@[expose] public section

/-!
# Prime and integral contributions of a cofactor

On each open cell of the real cofactor test, the quantitative prime number
theorem compares the prime count with the logarithmic integral. The finitely
many breakpoints contribute to the prime count and have measure zero.
-/

open Filter Asymptotics MeasureTheory Real Finset
open scoped BigOperators Interval

noncomputable section

namespace Erdos878

/-- Primes in the real open interval `(l, r)`. -/
def intervalPrimes (l r : ℝ) : Finset ℕ :=
  (primeBases ⌊r⌋₊).filter (fun p ↦ (p : ℝ) ∈ Set.Ioo l r)

theorem mem_intervalPrimes {l r : ℝ} {p : ℕ} :
    p ∈ intervalPrimes l r ↔ p.Prime ∧ (p : ℝ) ∈ Set.Ioo l r := by
  simp only [intervalPrimes, primeBases, mem_filter, mem_range, Nat.lt_succ_iff]
  refine ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨?_, h.1⟩, h.2⟩⟩
  exact (Nat.le_floor_iff' h.1.ne_zero).mpr h.2.2.le

open scoped Classical in
/-- Primes in the interval that pass the real cofactor test. -/
def goodIntervalPrimes (x m : ℕ) (l r : ℝ) : Finset ℕ :=
  (intervalPrimes l r).filter fun p ↦ cofactorGood x m p

theorem mem_goodIntervalPrimes {x m p : ℕ} {l r : ℝ} :
    p ∈ goodIntervalPrimes x m l r ↔
      p.Prime ∧ (p : ℝ) ∈ Set.Ioo l r ∧ cofactorGood x m p := by
  simp only [goodIntervalPrimes, mem_filter, mem_intervalPrimes, and_assoc]

/-- The cofactor count uses the same real open interval as its integral. -/
theorem cofactorPrimes_eq_goodIntervalPrimes (x m : ℕ) (Y : ℝ) (hm : 0 < m) :
    cofactorPrimes x m Y =
      goodIntervalPrimes x m (cofactorLower m Y) (cofactorUpper x m) := by
  classical
  ext p
  rw [mem_goodIntervalPrimes, cofactorPrimes, mem_filter, Nat.mem_primesBelow]
  refine ⟨fun ⟨⟨_, hp⟩, h⟩ ↦ ⟨hp, h⟩, fun ⟨hp, h⟩ ↦ ⟨⟨?_, hp⟩, h⟩⟩
  have hUp : cofactorUpper x m ≤ (x : ℝ) := by
    unfold cofactorUpper
    apply div_le_self (Nat.cast_nonneg _)
    exact_mod_cast hm
  exact_mod_cast h.1.2.trans_le hUp

/-- An open interval with reversed or coincident endpoints contains no primes. -/
theorem goodIntervalPrimes_eq_empty_of_ge {x m : ℕ} {l r : ℝ} (h : r ≤ l) :
    goodIntervalPrimes x m l r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hh := (mem_goodIntervalPrimes.mp hp).2.1
  exact h.not_gt (hh.1.trans hh.2)

/-- The logarithmic integral over the part of the interval passing the cofactor test. -/
def cofactorIntegral (x m : ℕ) (l r : ℝ) : ℝ :=
  ∫ u in {u | u ∈ Set.Ioo l r ∧ cofactorGood x m u}, (log u)⁻¹

/-- An open interval with reversed or coincident endpoints contributes zero. -/
theorem cofactorIntegral_eq_zero_of_ge {x m : ℕ} {l r : ℝ} (h : r ≤ l) :
    cofactorIntegral x m l r = 0 := by
  unfold cofactorIntegral
  rw [Set.Ioo_eq_empty_of_le h]
  simp

private theorem card_primeBases (n : ℕ) : (primeBases n).card = Nat.primeCounting n := by
  rw [primeBases, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

private theorem mem_primeBases_floor {p : ℕ} {z : ℝ} :
    p ∈ primeBases ⌊z⌋₊ ↔ p.Prime ∧ (p : ℝ) ≤ z := by
  simp only [primeBases, mem_filter, mem_range, Nat.lt_succ_iff]
  exact ⟨fun ⟨h, hp⟩ ↦ ⟨hp, (Nat.le_floor_iff' hp.ne_zero).mp h⟩,
    fun ⟨hp, h⟩ ↦ ⟨(Nat.le_floor_iff' hp.ne_zero).mpr h, hp⟩⟩

private theorem openInterval_count_error (a b : ℝ) (hab : a ≤ b) :
    |((intervalPrimes a b).card : ℝ) -
      ((Nat.primeCounting ⌊b⌋₊ : ℝ) - Nat.primeCounting ⌊a⌋₊)| ≤ 1 := by
  let A := primeBases ⌊a⌋₊
  let B := primeBases ⌊b⌋₊
  let S := intervalPrimes a b
  let T := B \ A
  have hAB : A ⊆ B := by
    intro p hp
    obtain ⟨hP, hp⟩ := mem_primeBases_floor.mp hp
    exact mem_primeBases_floor.mpr ⟨hP, hp.trans hab⟩
  have hm {p : ℕ} : p ∈ T ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
    have : p ∈ T ↔ (p.Prime ∧ (p : ℝ) ≤ b) ∧ ¬ (p.Prime ∧ (p : ℝ) ≤ a) := by
      change p ∈ B \ A ↔ _
      rw [Finset.mem_sdiff]
      simp only [B, A, mem_primeBases_floor]
    rw [this]
    constructor
    · exact fun ⟨⟨hp, hb⟩, hn⟩ ↦ ⟨hp, lt_of_not_ge (fun ha ↦ hn ⟨hp, ha⟩), hb⟩
    · exact fun ⟨hp, ha, hb⟩ ↦ ⟨⟨hp, hb⟩, fun h ↦ ha.not_ge h.2⟩
  have hST : S ⊆ T := by
    intro p hp
    obtain ⟨hp, ha, hb⟩ := mem_intervalPrimes.mp hp
    exact hm.mpr ⟨hp, ha, hb.le⟩
  have hrem : (T \ S).card ≤ 1 := by
    apply card_le_one_iff.mpr
    have hcast (p : ℕ) (hp : p ∈ T \ S) : (p : ℝ) = b := by
      obtain ⟨hpt, hps⟩ := mem_sdiff.mp hp
      obtain ⟨hP, ha, hb⟩ := hm.mp hpt
      exact hb.antisymm (le_of_not_gt (fun hb' ↦ hps (mem_intervalPrimes.mpr ⟨hP, ha, hb'⟩)))
    intro p q hp hq
    exact_mod_cast (hcast p hp).trans (hcast q hq).symm
  have hcard₁ := card_sdiff_add_card_eq_card hAB
  change T.card + A.card = B.card at hcard₁
  have hcard₂ := card_sdiff_add_card_eq_card hST
  have hcard₁R : (T.card : ℝ) + (A.card : ℝ) = (B.card : ℝ) := by exact_mod_cast hcard₁
  have hcard₂R : ((T \ S).card : ℝ) + (S.card : ℝ) = (T.card : ℝ) := by exact_mod_cast hcard₂
  have heq : (S.card : ℝ) - ((B.card : ℝ) - A.card) = -(↑(T \ S).card : ℝ) := by linarith
  change |(S.card : ℝ) - ((Nat.primeCounting ⌊b⌋₊ : ℝ) - Nat.primeCounting ⌊a⌋₊)| ≤ 1
  rw [← card_primeBases, ← card_primeBases]
  change |(S.card : ℝ) - ((B.card : ℝ) - A.card)| ≤ 1
  rw [heq, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hrem

private theorem li_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ ↦ (log u)⁻¹) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  refine ContinuousOn.integrableOn_Icc fun u hu ↦ ContinuousAt.continuousWithinAt ?_
  have hup : 0 < u := by linarith [hu.1]
  have hlog : 0 < log u := log_pos (by linarith [hu.1])
  fun_prop (disch := positivity)

private theorem intervalApproximation :
    ∃ c > 0, ∃ D > 0, ∃ A ≥ 2, ∀ l r a b : ℝ, A ≤ l → l ≤ a → a < b → b ≤ r →
      |((intervalPrimes a b).card : ℝ) - ∫ u in a..b, (log u)⁻¹| ≤
        2 * D * (r * exp (-c * log l ^ (1 / 10 : ℝ))) + 1 := by
  obtain ⟨c, hc, hPNT⟩ := primeCounting_sub_li_isBigO
  obtain ⟨D, hD, hPNT⟩ := hPNT.exists_pos
  obtain ⟨A, hA⟩ := eventually_atTop.1 hPNT.bound
  refine ⟨c, hc, D, hD, max A 2, le_max_right _ _, ?_⟩
  intro l r a b hl hla hab hbr
  have hl2 : 2 ≤ l := (le_max_right A 2).trans hl
  have ha2 : 2 ≤ a := hl2.trans hla
  have hb2 : 2 ≤ b := ha2.trans hab.le
  let Z := r * exp (-c * log l ^ (1 / 10 : ℝ))
  let P (t : ℝ) : ℝ := Nat.primeCounting ⌊t⌋₊
  let L (t : ℝ) : ℝ := ∫ u in 2..t, (log u)⁻¹
  have hbound (t : ℝ) (hlt : l ≤ t) (htr : t ≤ r) : |P t - L t| ≤ D * Z := by
    have ht0 : 0 ≤ t := by linarith
    have ht : A ≤ t := (le_max_left A 2).trans (hl.trans hlt)
    have hs := hA t ht
    have hdec : exp (-c * log t ^ (1 / 10 : ℝ)) ≤ exp (-c * log l ^ (1 / 10 : ℝ)) := by
      have hlog := log_le_log (by linarith : 0 < l) hlt
      have hpow := rpow_le_rpow (log_nonneg (by linarith : 1 ≤ l)) hlog
        (by norm_num : (0 : ℝ) ≤ 1 / 10)
      apply exp_le_exp.mpr
      nlinarith
    have hr0 : 0 ≤ r := ht0.trans htr
    have hZ : t * exp (-c * log t ^ (1 / 10 : ℝ)) ≤ Z := by
      exact mul_le_mul htr hdec (exp_nonneg _) hr0
    have hprod : 0 ≤ t * exp (-c * log t ^ (1 / 10 : ℝ)) := by positivity
    change ‖P t - L t‖ ≤ D * ‖t * exp (-c * log t ^ (1 / 10 : ℝ))‖ at hs
    simpa only [Real.norm_eq_abs, abs_of_nonneg hprod] using
      hs.trans (by rw [Real.norm_of_nonneg hprod]; exact mul_le_mul_of_nonneg_left hZ hD.le)
  have hli : ∫ u in a..b, (log u)⁻¹ = L b - L a := by
    dsimp [L]
    have h := intervalIntegral.integral_add_adjacent_intervals
      (li_intervalIntegrable (by norm_num : (2 : ℝ) ≤ 2) ha2)
      (li_intervalIntegrable ha2 hab.le)
    linarith
  have hct := openInterval_count_error a b hab.le
  rw [hli]
  calc
    _ = |(((intervalPrimes a b).card : ℝ) - (P b - P a)) +
      ((P b - L b) - (P a - L a))| := by congr 1; ring
    _ ≤ |((intervalPrimes a b).card : ℝ) - (P b - P a)| +
      (|P b - L b| + |P a - L a|) := by
      exact (abs_add_le ..).trans (add_le_add le_rfl (by
        rw [← abs_neg (P a - L a), sub_eq_add_neg]
        exact abs_add_le ..))
    _ ≤ 1 + (D * Z + D * Z) :=
      add_le_add hct (add_le_add (hbound b (hla.trans hab.le) hbr) (hbound a hla (hab.le.trans hbr)))
    _ = _ := by dsimp [Z]; ring

private theorem cell_bounds {x m : ℕ} {l r : ℝ} {ab : ℝ × ℝ}
    (h : ab ∈ cofactorCells x m l r) : l ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ r := by
  have h' := mem_cofactorCells_iff.mp h
  exact ⟨(mem_Icc_of_mem_cofactorBreaks h'.1.1).1, h'.2.1,
    (mem_Icc_of_mem_cofactorBreaks h'.1.2).2⟩

/-- Only the passing open cells contribute to the value of the cofactor integral. -/
theorem cofactorIntegral_eq_sum {x m : ℕ} {l r : ℝ} (hl : 2 ≤ l) :
    cofactorIntegral x m l r =
      ∑ ab ∈ cofactorCells x m l r, ∫ u in ab.1..ab.2, (log u)⁻¹ := by
  classical
  let C := cofactorCells x m l r
  let J (ab : ℝ × ℝ) := Set.Ioo ab.1 ab.2
  have hno : ∀ᵐ u : ℝ ∂volume, u ∉ cofactorBreaks x m l r := by
    rw [ae_iff]
    simpa using (cofactorBreaks x m l r).finite_toSet.measure_zero (volume : Measure ℝ)
  have hs : {u | u ∈ Set.Ioo l r ∧ cofactorGood x m u} =ᵐ[volume] ⋃ ab ∈ C, J ab := by
    filter_upwards [hno] with u hu
    apply propext
    change (u ∈ Set.Ioo l r ∧ cofactorGood x m u) ↔ u ∈ ⋃ ab ∈ C, J ab
    simp only [Set.mem_iUnion]
    constructor
    · intro ⟨h, hg⟩
      obtain ⟨ab, hab, hmem⟩ := exists_cofactorCell_of_good h hu hg
      exact ⟨ab, hab, hmem⟩
    · intro h
      obtain ⟨ab, hab, h⟩ := h
      have hb := cell_bounds hab
      exact ⟨⟨hb.1.trans_lt h.1, h.2.trans_le hb.2.2⟩, cofactorGood_of_mem_cofactorCell hab h⟩
  unfold cofactorIntegral
  rw [setIntegral_congr_set hs]
  have hInt (ab : ℝ × ℝ) (hab : ab ∈ C) :
      IntegrableOn (fun u : ℝ ↦ (log u)⁻¹) (J ab) volume := by
    have h := cell_bounds hab
    apply IntegrableOn.mono_set ?_ Set.Ioo_subset_Icc_self
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le h.2.1.le).mp
      (li_intervalIntegrable (hl.trans h.1) h.2.1.le)
  rw [integral_biUnion_finset C (fun _ _ ↦ measurableSet_Ioo)
    (cofactorCells_pairwiseDisjoint x m l r) hInt]
  refine sum_congr rfl (fun ab hab ↦ ?_)
  have h := cell_bounds hab
  rw [intervalIntegral.integral_of_le h.2.1.le, integral_Ioc_eq_integral_Ioo]

private theorem card_goodIntervalPrimes_sub_cell_counts (x m : ℕ) (l r : ℝ) :
    |((goodIntervalPrimes x m l r).card : ℝ) -
      ∑ ab ∈ cofactorCells x m l r, ((intervalPrimes ab.1 ab.2).card : ℝ)| ≤
        ((cofactorBreaks x m l r).card : ℝ) := by
  classical
  let C := cofactorCells x m l r
  let s := goodIntervalPrimes x m l r
  let t (ab : ℝ × ℝ) := intervalPrimes ab.1 ab.2
  let U := C.biUnion t
  have hdisj : Set.PairwiseDisjoint (C : Set (ℝ × ℝ)) t := by
    intro ab hab cd hcd hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := cofactorCells_pairwiseDisjoint x m l r hab hcd hne
    exact Set.disjoint_left.mp h (mem_intervalPrimes.mp hp).2 (mem_intervalPrimes.mp hq).2
  have hcard : (U.card : ℝ) = ∑ ab ∈ C, ((t ab).card : ℝ) := by
    dsimp [U]
    exact_mod_cast Finset.card_biUnion hdisj
  have hUs : U ⊆ s := by
    intro p hp
    obtain ⟨ab, hab, hp⟩ := mem_biUnion.mp hp
    obtain ⟨hp, hpa, hpb⟩ := mem_intervalPrimes.mp hp
    have hh := cell_bounds hab
    exact mem_goodIntervalPrimes.mpr
      ⟨hp, ⟨hh.1.trans_lt hpa, hpb.trans_le hh.2.2⟩,
        cofactorGood_of_mem_cofactorCell hab ⟨hpa, hpb⟩⟩
  have hrest : (s \ U).card ≤ (cofactorBreaks x m l r).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ ↦ (p : ℝ)) _ Nat.cast_injective.injOn
    intro p hp
    obtain ⟨hp, hnot⟩ := mem_sdiff.mp hp
    obtain ⟨hpp, hp, hg⟩ := mem_goodIntervalPrimes.mp hp
    by_contra! hn
    obtain ⟨ab, hab, h⟩ := exists_cofactorCell_of_good hp hn hg
    exact hnot (mem_biUnion.mpr ⟨ab, hab, mem_intervalPrimes.mpr ⟨hpp, h⟩⟩)
  have hsum := card_sdiff_add_card_eq_card hUs
  have hsumR : ((s \ U).card : ℝ) + (U.card : ℝ) = (s.card : ℝ) := by exact_mod_cast hsum
  have heq : (s.card : ℝ) - (U.card : ℝ) = ((s \ U).card : ℝ) := by linarith
  change |(s.card : ℝ) - ∑ ab ∈ C, ((t ab).card : ℝ)| ≤ _
  rw [← hcard, heq, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hrest

/-- Quantitative comparison between the prime and logarithmic-integral contributions
of each cofactor. -/
theorem cofactorApproximation :
    ∃ c > 0, ∃ C > 0, ∃ A ≥ 2, ∀ (x m : ℕ) (l r : ℝ), A ≤ l → l < r →
      |((goodIntervalPrimes x m l r).card : ℝ) - cofactorIntegral x m l r| ≤
        C * (r * exp (-c * log l ^ (1 / 10 : ℝ)) + 1) * (cofactorCellBound x m : ℝ) ^ 2 := by
  obtain ⟨c, hc, D, hD, A, hA, hi⟩ := intervalApproximation
  refine ⟨c, hc, 2 * D + 2, by positivity, A, hA, ?_⟩
  intro x m l r hl hlr
  let Z := r * exp (-c * log l ^ (1 / 10 : ℝ))
  let B : ℝ := (cofactorCellBound x m : ℝ) ^ 2
  let C := cofactorCells x m l r
  let N (ab : ℝ × ℝ) : ℝ := (intervalPrimes ab.1 ab.2).card
  let L (ab : ℝ × ℝ) : ℝ := ∫ u in ab.1..ab.2, (log u)⁻¹
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hr : 0 < r := (by linarith [hA.trans hl] : 0 < l).trans hlr
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hcardB : (C.card : ℝ) ≤ B := by dsimp [C, B]; exact_mod_cast card_cofactorCells_le x m l r
  have hbreakB : ((cofactorBreaks x m l r).card : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast (card_cofactorBreaks_le x m l r).trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  have hsum :
      |∑ ab ∈ C, (N ab - L ab)| ≤ B * (2 * D * Z + 1) := by
    calc
      _ ≤ ∑ ab ∈ C, |N ab - L ab| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ C, (2 * D * Z + 1) := by
        refine sum_le_sum (fun ab hab ↦ ?_)
        obtain ⟨h₁, h₂, h₃⟩ := cell_bounds hab
        exact hi l r ab.1 ab.2 hl h₁ h₂ h₃
      _ = (C.card : ℝ) * (2 * D * Z + 1) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardB (by positivity)
  rw [cofactorIntegral_eq_sum (hA.trans hl)]
  change |((goodIntervalPrimes x m l r).card : ℝ) - ∑ ab ∈ C, L ab| ≤ _
  calc
    _ = |(((goodIntervalPrimes x m l r).card : ℝ) - ∑ ab ∈ C, N ab) +
      ∑ ab ∈ C, (N ab - L ab)| := by rw [sum_sub_distrib]; congr 1; ring
    _ ≤ |((goodIntervalPrimes x m l r).card : ℝ) - ∑ ab ∈ C, N ab| +
      |∑ ab ∈ C, (N ab - L ab)| := abs_add_le _ _
    _ ≤ B + B * (2 * D * Z + 1) :=
      add_le_add ((card_goodIntervalPrimes_sub_cell_counts ..).trans hbreakB) hsum
    _ ≤ _ := by
      change B + B * (2 * D * Z + 1) ≤ (2 * D + 2) * (Z + 1) * B
      nlinarith [mul_nonneg hB0 hD.le, mul_nonneg hB0 hZ]

#print axioms cofactorApproximation

end Erdos878
