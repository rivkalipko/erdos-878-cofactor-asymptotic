module

public import Erdos878Proofs.CofactorCount
public import Erdos878Proofs.DiscardSmooth

@[expose] public section

/-! # Exceptional integers in the largest-prime decomposition -/

namespace Erdos878

open scoped Classical

private theorem retained_subset_equalities (x : ℕ) :
    retainedEqualities x (omegaCutoff x) (cofactorThreshold x) ⊆
      (Finset.Ico 1 x).filter (fun n ↦ f n = F n) := by
  intro n hn
  obtain ⟨hnx, heq, _⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hnx, heq⟩

/-- An equality integer omitted from the decomposition lies in one of the three
exceptional families. -/
theorem mem_exception_of_not_retained {x n : ℕ} (hn : n ∈ Finset.Ico 1 x)
    (heq : f n = F n)
    (hret : n ∉ retainedEqualities x (omegaCutoff x) (cofactorThreshold x)) :
    n ∈ x.smoothNumbersUpTo (smoothCutoff x) ∨
      n ∈ largeSquareDivisor x ∨ n ∈ manyPrimeFactors x := by
  obtain ⟨hnpos, hnx⟩ := Finset.mem_Ico.mp hn
  by_cases hcard : n.primeFactors.card ≤ omegaCutoff x + 1
  · by_cases hsmooth : ∀ p ∈ n.primeFactors, (p : ℝ) ≤ cofactorThreshold x
    · left
      apply Nat.mem_smoothNumbersUpTo.mpr
      refine ⟨hnx.le, Nat.mem_smoothNumbers_of_primeFactors_subset (by omega) ?_⟩
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hsmooth p hp)))
    · push Not at hsmooth
      obtain ⟨p, hp, hpY⟩ := hsmooth
      let hpnonempty : n.primeFactors.Nonempty := ⟨p, hp⟩
      let q := n.primeFactors.max' hpnonempty
      have hq : q ∈ n.primeFactors := Finset.max'_mem _ _
      have hmax : ∀ r ∈ n.primeFactors, r ≤ q := fun r hr ↦ Finset.le_max' _ r hr
      have hqY : cofactorThreshold x < (q : ℝ) :=
        hpY.trans_le (by exact_mod_cast hmax p hp)
      have hqSquare : q ^ 2 ∣ n := by
        by_contra! hsq
        exact hret (Finset.mem_filter.mpr ⟨hn, heq, hcard, q, hq, hqY, hmax, hsq⟩)
      have hqRange : q ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hq).one_le,
          (Nat.le_of_mem_primeFactors hq).trans hnx.le⟩
      exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hn, q, hqRange, hqY, hqSquare⟩))
  · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hn, by omega⟩))

/-- The count lost in the cofactor decomposition is bounded by the sum of the
three exceptional counts. -/
theorem abs_E_sub_retained_le (x : ℕ) :
    |E x - ((retainedEqualities x (omegaCutoff x) (cofactorThreshold x)).card : ℝ)| ≤
      ((x.smoothNumbersUpTo (smoothCutoff x)).card : ℝ) +
        (largeSquareDivisor x).card + (manyPrimeFactors x).card := by
  let eqSet := (Finset.Ico 1 x).filter (fun n ↦ f n = F n)
  let ret := retainedEqualities x (omegaCutoff x) (cofactorThreshold x)
  let smooth := x.smoothNumbersUpTo (smoothCutoff x)
  let squares := largeSquareDivisor x
  let many := manyPrimeFactors x
  have hret : ret ⊆ eqSet := retained_subset_equalities x
  have hcard := Finset.card_le_card hret
  change |(eqSet.card : ℝ) - (ret.card : ℝ)| ≤
    (smooth.card : ℝ) + (squares.card : ℝ) + (many.card : ℝ)
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hcard)), ← Nat.cast_sub hcard,
      ← Finset.card_sdiff_of_subset hret]
  have hcover : eqSet \ ret ⊆ smooth ∪ squares ∪ many := by
    intro n hn
    obtain ⟨heqSet, hnret⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnx, heq⟩ := Finset.mem_filter.mp heqSet
    rcases mem_exception_of_not_retained hnx heq hnret with hs | hsq | hm
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hs)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hsq)
    · exact Finset.mem_union_right _ hm
  have hunion : (eqSet \ ret).card ≤ smooth.card + squares.card + many.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  exact_mod_cast hunion

end Erdos878
