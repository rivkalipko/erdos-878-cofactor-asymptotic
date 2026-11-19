module

public import Erdos878Proofs.Cofactor

@[expose] public section

/-!
# Polynomial intervals for the cofactor construction

The cofactor inequalities are constant off the roots of finitely many polynomials.
-/

namespace Erdos878

open scoped BigOperators Polynomial Classical
open Polynomial

private noncomputable def basePoly (m : ℕ) : CofactorIndex m → ℝ[X]
  | none => X
  | some p => C (p.val : ℝ)

private theorem eval_basePoly (m : ℕ) (u : ℝ) (i : CofactorIndex m) :
    (basePoly m i).eval u = cofactorBase m u i := by
  cases i <;> simp [basePoly, cofactorBase]

private theorem natDegree_basePoly_le (m : ℕ) (i : CofactorIndex m) :
    (basePoly m i).natDegree ≤ 1 := by
  cases i <;> simp [basePoly]

private noncomputable def valuePoly (x m : ℕ) (a : CofactorExponents x m) : ℝ[X] :=
  C (∏ p : {p : ℕ // p ∈ m.primeFactors}, (p.val : ℝ) ^ (a (some p)).val) *
    X ^ (a none).val

private theorem eval_valuePoly (x m : ℕ) (u : ℝ) (a : CofactorExponents x m) :
    (valuePoly x m a).eval u = cofactorValue x m u a := by
  simp only [valuePoly, cofactorValue, Fintype.prod_option, cofactorBase,
    eval_mul, eval_C, eval_pow, eval_X, mul_comm]

private theorem natDegree_valuePoly_le (x m : ℕ) (a : CofactorExponents x m) :
    (valuePoly x m a).natDegree ≤ Nat.log 2 x + 1 := by
  unfold valuePoly
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
  exact (a none).isLt.le

private noncomputable def limitPoly (m : ℕ) : ℝ[X] := C (m : ℝ) * X

private theorem eval_limitPoly (m : ℕ) (u : ℝ) : (limitPoly m).eval u = (m : ℝ) * u := by
  simp [limitPoly]

private theorem natDegree_limitPoly_le (x m : ℕ) :
    (limitPoly m).natDegree ≤ Nat.log 2 x + 1 := by
  unfold limitPoly
  refine Polynomial.natDegree_mul_le.trans ?_
  simp

private noncomputable def supportPoly (x m : ℕ) (a e : CofactorExponents x m) : ℝ[X] :=
  ∑ i, if (a i).val = 0 then 0 else basePoly m i ^ (e i).val

private theorem eval_supportPoly (x m : ℕ) (u : ℝ) (a e : CofactorExponents x m) :
    (supportPoly x m a e).eval u =
      ∑ i, if (a i).val = 0 then 0 else cofactorBase m u i ^ (e i).val := by
  simp only [supportPoly, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : (a i).val = 0 <;> simp [ha, eval_basePoly]

private theorem natDegree_basePow_le (x m : ℕ) (i : CofactorIndex m)
    (k : Fin (Nat.log 2 x + 1)) :
    (basePoly m i ^ k.val).natDegree ≤ Nat.log 2 x + 1 := by
  refine Polynomial.natDegree_pow_le.trans ?_
  calc
    _ ≤ k.val * 1 := Nat.mul_le_mul_left _ (natDegree_basePoly_le m i)
    _ ≤ _ := by
      rw [Nat.mul_one]
      exact k.isLt.le

private theorem natDegree_supportPoly_le (x m : ℕ) (a e : CofactorExponents x m) :
    (supportPoly x m a e).natDegree ≤ Nat.log 2 x + 1 := by
  unfold supportPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  split_ifs
  · simp
  · exact natDegree_basePow_le x m i (e i)

private abbrev AtomIndex (x m : ℕ) :=
  CofactorExponents x m ⊕ (CofactorExponents x m ⊕
    ((CofactorIndex m × Fin (Nat.log 2 x + 1)) ⊕
      (CofactorExponents x m × CofactorExponents x m)))

private noncomputable def atomPoly (x m : ℕ) : AtomIndex x m → ℝ[X]
  | .inl a => C 2 - valuePoly x m a
  | .inr (.inl a) => valuePoly x m a - limitPoly m
  | .inr (.inr (.inl (i, k))) => basePoly m i ^ k.val - limitPoly m
  | .inr (.inr (.inr (a, e))) => valuePoly x m a - supportPoly x m a e

private theorem natDegree_atomPoly_le (x m : ℕ) (j : AtomIndex x m) :
    (atomPoly x m j).natDegree ≤ Nat.log 2 x + 1 := by
  rcases j with a | a | ⟨i, k⟩ | ⟨a, e⟩
  · simpa only [atomPoly, max_self] using
      natDegree_sub_le_of_le (n := Nat.log 2 x + 1)
        (show (C (2 : ℝ)).natDegree ≤ Nat.log 2 x + 1 by simp)
        (natDegree_valuePoly_le x m a)
  · simpa only [atomPoly, max_self] using
      natDegree_sub_le_of_le (natDegree_valuePoly_le x m a) (natDegree_limitPoly_le x m)
  · simpa only [atomPoly, max_self] using
      natDegree_sub_le_of_le (natDegree_basePow_le x m i k) (natDegree_limitPoly_le x m)
  · simpa only [atomPoly, max_self] using
      natDegree_sub_le_of_le (natDegree_valuePoly_le x m a) (natDegree_supportPoly_le x m a e)

private noncomputable def cofactorRoots (x m : ℕ) : Finset ℝ :=
  Finset.univ.biUnion fun j : AtomIndex x m ↦ (atomPoly x m j).roots.toFinset

/-- A bound on the number of polynomial roots and outer endpoints in the cofactor test. -/
def cofactorCellBound (x m : ℕ) : ℕ :=
  let B := Nat.log 2 x + 1
  let D := m.primeFactors.card + 1
  let V := B ^ D
  (V + (V + (D * B + V * V))) * B + 2

private theorem roots_card_le (x m : ℕ) : (cofactorRoots x m).card + 2 ≤ cofactorCellBound x m := by
  unfold cofactorRoots cofactorCellBound
  apply Nat.add_le_add_right
  have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (AtomIndex x m))
    (fun j ↦ (atomPoly x m j).roots.toFinset) (Nat.log 2 x + 1)
    (fun j _ ↦ (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (natDegree_atomPoly_le x m j)))
  simpa [AtomIndex, CofactorExponents, CofactorIndex, add_comm] using h

/-- The outer endpoints and all roots in the open cofactor interval. -/
@[no_expose]
noncomputable def cofactorBreaks (x m : ℕ) (l u : ℝ) : Finset ℝ :=
  if l < u then insert l (insert u ((cofactorRoots x m).filter fun z ↦ z ∈ Set.Ioo l u)) else ∅

theorem card_cofactorBreaks_le (x m : ℕ) (l u : ℝ) :
    (cofactorBreaks x m l u).card ≤ cofactorCellBound x m := by
  unfold cofactorBreaks
  split_ifs
  · refine le_trans (Finset.card_insert_le _ _) ?_
    refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_filter_le _ _) 1) 1) ?_
    simpa [Nat.add_assoc] using roots_card_le x m
  · simp

private theorem outer_endpoints_mem {x m : ℕ} {l u : ℝ} (h : l < u) :
    l ∈ cofactorBreaks x m l u ∧ u ∈ cofactorBreaks x m l u := by
  simp [cofactorBreaks, h]

theorem mem_Icc_of_mem_cofactorBreaks {x m : ℕ} {l u z : ℝ}
    (hz : z ∈ cofactorBreaks x m l u) : z ∈ Set.Icc l u := by
  by_cases h : l < u
  · simp only [cofactorBreaks, ite_eq_left h, Finset.mem_insert, Finset.mem_filter] at hz
    rcases hz with rfl | rfl | ⟨_, hz⟩
    · exact ⟨le_rfl, h.le⟩
    · exact ⟨h.le, le_rfl⟩
    · exact ⟨hz.1.le, hz.2.le⟩
  · simp [cofactorBreaks, h] at hz

private theorem no_root_between {x m : ℕ} {l u a b z : ℝ} (hl : l ≤ a) (hu : b ≤ u)
    (hgap : ∀ w ∈ cofactorBreaks x m l u, w ∉ Set.Ioo a b)
    (j : AtomIndex x m) (hz : z ∈ Set.Ioo a b) (hp : atomPoly x m j ≠ 0) :
    (atomPoly x m j).eval z ≠ 0 := by
  intro he
  apply hgap z _ hz
  rw [cofactorBreaks, ite_eq_left (hl.trans_lt (hz.1.trans (hz.2.trans_le hu)))]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr ?_⟩,
    hl.trans_lt hz.1, hz.2.trans_le hu⟩
  exact (Polynomial.mem_roots hp).mpr he

private theorem polynomial_sign_equiv_on_Ioo {P : ℝ[X]} {a b v w : ℝ}
    (hv : v ∈ Set.Ioo a b) (hw : w ∈ Set.Ioo a b)
    (hn : P ≠ 0 → ∀ z ∈ Set.Ioo a b, P.eval z ≠ 0) :
    P.eval v ≤ 0 ↔ P.eval w ≤ 0 := by
  by_cases hp : P = 0
  · simp [hp]
  have noOpposite {y z : ℝ} (hy : y ∈ Set.Ioo a b) (hz : z ∈ Set.Ioo a b)
      (hyn : P.eval y ≤ 0) (hzp : 0 ≤ P.eval z) : False := by
    have himage := isPreconnected_Ioo.intermediate_value hy hz
      P.continuous.continuousOn (show (0 : ℝ) ∈ Set.Icc (P.eval y) (P.eval z) from ⟨hyn, hzp⟩)
    obtain ⟨t, ht, he⟩ := himage
    exact hn hp t ht he
  exact ⟨fun h ↦ le_of_not_gt fun h' ↦ noOpposite hv hw h h'.le,
    fun h ↦ le_of_not_gt fun h' ↦ noOpposite hw hv h h'.le⟩

private theorem exp_le_bound (x : ℕ) (b n : ℝ) :
    realPrimeExponent x b n ≤ Nat.log 2 x := by
  unfold realPrimeExponent
  apply Finset.sup_le
  intro k hk
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)

private theorem cofactorGood_congr {x m : ℕ} {v w : ℝ}
    (h : ∀ j : AtomIndex x m, (atomPoly x m j).eval v ≤ 0 ↔ (atomPoly x m j).eval w ≤ 0) :
    cofactorGood x m v ↔ cofactorGood x m w := by
  let e : CofactorExponents x m := fun i ↦
    ⟨realPrimeExponent x (cofactorBase m v i) ((m : ℝ) * v),
      Nat.lt_succ_of_le (exp_le_bound _ _ _)⟩
  have he (i : CofactorIndex m) :
      (e i).val = realPrimeExponent x (cofactorBase m w i) ((m : ℝ) * w) := by
    change realPrimeExponent x _ _ = realPrimeExponent x _ _
    unfold realPrimeExponent
    congr 1
    ext k
    simp only [Finset.mem_filter]
    by_cases hk : k ∈ Finset.range (Nat.log 2 x + 1)
    · have hj := h (.inr (.inr (.inl (i, ⟨k, Finset.mem_range.mp hk⟩))))
      simpa [hk, atomPoly, eval_basePoly, eval_limitPoly, sub_nonpos] using hj
    · simp [hk]
  have low (a : CofactorExponents x m) :
      2 ≤ cofactorValue x m v a ↔ 2 ≤ cofactorValue x m w a := by
    simpa [atomPoly, eval_valuePoly, sub_nonpos] using h (.inl a)
  have limit (a : CofactorExponents x m) :
      cofactorValue x m v a ≤ (m : ℝ) * v ↔ cofactorValue x m w a ≤ (m : ℝ) * w := by
    simpa [atomPoly, eval_valuePoly, eval_limitPoly, sub_nonpos] using h (.inr (.inl a))
  have gain (a : CofactorExponents x m) := h (.inr (.inr (.inr (a, e))))
  simp only [atomPoly, eval_sub, eval_valuePoly, eval_supportPoly, sub_nonpos] at gain
  constructor
  · intro hv a ha hl
    have hv' := hv a ((low a).mpr ha) ((limit a).mpr hl)
    have hw := (gain a).mp hv'
    simpa only [he] using hw
  · intro hw a ha hl
    have hw' := hw a ((low a).mp ha) ((limit a).mp hl)
    apply (gain a).mpr
    simpa only [he] using hw'

private theorem cofactorGood_equiv_on_gap {x m : ℕ} {l u a b v w : ℝ}
    (hl : l ≤ a) (hu : b ≤ u)
    (hgap : ∀ z ∈ cofactorBreaks x m l u, z ∉ Set.Ioo a b)
    (hv : v ∈ Set.Ioo a b) (hw : w ∈ Set.Ioo a b) :
    cofactorGood x m v ↔ cofactorGood x m w := by
  apply cofactorGood_congr
  intro j
  exact polynomial_sign_equiv_on_Ioo hv hw (fun hp z hz ↦ no_root_between hl hu hgap j hz hp)

/-- Consecutive breakpoint pairs whose open interval passes the real cofactor test. -/
noncomputable def cofactorCells (x m : ℕ) (l u : ℝ) : Finset (ℝ × ℝ) :=
  ((cofactorBreaks x m l u) ×ˢ (cofactorBreaks x m l u)).filter fun ab ↦
    ab.1 < ab.2 ∧
      (∀ z ∈ cofactorBreaks x m l u, z ∉ Set.Ioo ab.1 ab.2) ∧
      cofactorGood x m ((ab.1 + ab.2) / 2)

theorem mem_cofactorCells_iff {x m : ℕ} {l u : ℝ} {ab : ℝ × ℝ} :
    ab ∈ cofactorCells x m l u ↔
      (ab.1 ∈ cofactorBreaks x m l u ∧ ab.2 ∈ cofactorBreaks x m l u) ∧
      ab.1 < ab.2 ∧ (∀ z ∈ cofactorBreaks x m l u, z ∉ Set.Ioo ab.1 ab.2) ∧
        cofactorGood x m ((ab.1 + ab.2) / 2) := by
  simp only [cofactorCells, Finset.mem_filter, Finset.mem_product]

theorem card_cofactorCells_le (x m : ℕ) (l u : ℝ) :
    (cofactorCells x m l u).card ≤ cofactorCellBound x m ^ 2 := by
  unfold cofactorCells
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_product, pow_two]
  exact Nat.mul_le_mul (card_cofactorBreaks_le x m l u) (card_cofactorBreaks_le x m l u)

theorem cofactorCells_pairwiseDisjoint (x m : ℕ) (l u : ℝ) :
    Set.PairwiseDisjoint (cofactorCells x m l u : Set (ℝ × ℝ))
      (fun ab : ℝ × ℝ ↦ Set.Ioo ab.1 ab.2) := by
  intro ab hab cd hcd hne
  have hab' := mem_cofactorCells_iff.mp hab
  have hcd' := mem_cofactorCells_iff.mp hcd
  apply Set.disjoint_left.mpr
  intro y hy hz
  apply hne
  apply Prod.ext
  · apply le_antisymm
    · exact le_of_not_gt (fun h ↦ hcd'.2.2.1 _ hab'.1.1 ⟨h, hy.1.trans hz.2⟩)
    · exact le_of_not_gt (fun h ↦ hab'.2.2.1 _ hcd'.1.1 ⟨h, hz.1.trans hy.2⟩)
  · apply le_antisymm
    · exact le_of_not_gt (fun h ↦ hab'.2.2.1 _ hcd'.1.2 ⟨hy.1.trans hz.2, h⟩)
    · exact le_of_not_gt (fun h ↦ hcd'.2.2.1 _ hab'.1.2 ⟨hz.1.trans hy.2, h⟩)

theorem cofactorGood_of_mem_cofactorCell {x m : ℕ} {l u y : ℝ} {ab : ℝ × ℝ}
    (ha : ab ∈ cofactorCells x m l u) (hy : y ∈ Set.Ioo ab.1 ab.2) : cofactorGood x m y := by
  have ha' := mem_cofactorCells_iff.mp ha
  have hl := (mem_Icc_of_mem_cofactorBreaks ha'.1.1).1
  have hu := (mem_Icc_of_mem_cofactorBreaks ha'.1.2).2
  have hmid : (ab.1 + ab.2) / 2 ∈ Set.Ioo ab.1 ab.2 := by
    constructor <;> linarith [ha'.2.1]
  exact (cofactorGood_equiv_on_gap hl hu ha'.2.2.1 hmid hy).mp ha'.2.2.2

theorem exists_cofactorCell_of_good {x m : ℕ} {l u y : ℝ} (hy : y ∈ Set.Ioo l u)
    (hn : y ∉ cofactorBreaks x m l u) (hg : cofactorGood x m y) :
    ∃ ab ∈ cofactorCells x m l u, y ∈ Set.Ioo ab.1 ab.2 := by
  let s := cofactorBreaks x m l u
  have hou := outer_endpoints_mem (x := x) (m := m) (hy.1.trans hy.2)
  let left := s.filter (· < y)
  let right := s.filter (y < ·)
  have hl : left.Nonempty := ⟨l, Finset.mem_filter.mpr ⟨hou.1, hy.1⟩⟩
  have hr : right.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨hou.2, hy.2⟩⟩
  let a := left.max' hl
  let b := right.min' hr
  have ha := Finset.mem_filter.mp (Finset.max'_mem left hl)
  have hb := Finset.mem_filter.mp (Finset.min'_mem right hr)
  have hgap : ∀ z ∈ s, z ∉ Set.Ioo a b := by
    intro z hz hg'
    rcases lt_trichotomy z y with hlt | rfl | hgt
    · exact (not_lt_of_ge (Finset.le_max' left z (Finset.mem_filter.mpr ⟨hz, hlt⟩))) hg'.1
    · exact hn hz
    · exact (not_lt_of_ge (Finset.min'_le right z (Finset.mem_filter.mpr ⟨hz, hgt⟩))) hg'.2
  refine ⟨(a, b), mem_cofactorCells_iff.mpr ⟨⟨ha.1, hb.1⟩, ha.2.trans hb.2, hgap, ?_⟩,
    ha.2, hb.2⟩
  have hmid : (a + b) / 2 ∈ Set.Ioo a b := by
    exact ⟨by linarith [ha.2, hb.2], by linarith [ha.2, hb.2]⟩
  exact (cofactorGood_equiv_on_gap (mem_Icc_of_mem_cofactorBreaks ha.1).1
    (mem_Icc_of_mem_cofactorBreaks hb.1).2 hgap ⟨ha.2, hb.2⟩ hmid).mp hg

/-- A convenient exponential upper bound for estimates involving the number of cells. -/
theorem cofactorCellBound_le {x m : ℕ} (hx : 2 ≤ x) :
    cofactorCellBound x m ≤ 6 * (Nat.log 2 x + 1) ^ (2 * (m.primeFactors.card + 1) + 1) := by
  let B := Nat.log 2 x + 1
  let D := m.primeFactors.card + 1
  let V := B ^ D
  have hB : 2 ≤ B := by
    have := Nat.le_log_of_pow_le (by decide : 1 < (2 : ℕ)) (show 2 ^ 1 ≤ x by simpa using hx)
    dsimp [B]
    omega
  have hD : D ≠ 0 := by simp [D]
  have hBV : B ≤ V := Nat.le_self_pow hD _
  have hDV : D ≤ V := D.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hB _)
  have hV : 1 ≤ V := (show 1 ≤ B by omega).trans hBV
  have hV2 : V ≤ V * V := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left V hV
  have hDB : D * B ≤ V * V := Nat.mul_le_mul hDV hBV
  have hsum : V + (V + (D * B + V * V)) ≤ 4 * (V * V) := by omega
  have hpos : 1 ≤ B * (V * V) := by
    exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  calc
    cofactorCellBound x m = (V + (V + (D * B + V * V))) * B + 2 := rfl
    _ ≤ (4 * (V * V)) * B + 2 := Nat.add_le_add_right (Nat.mul_le_mul_right B hsum) _
    _ ≤ 6 * (B * (V * V)) := by
      rw [show (4 * (V * V)) * B = 4 * (B * (V * V)) by ring]
      omega
    _ = 6 * B ^ (2 * D + 1) := by
      rw [show 2 * D = D + D by omega, pow_succ, pow_add]
      dsimp [V]
      ring

end Erdos878
