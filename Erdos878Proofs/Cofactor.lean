module

public import Erdos878Proofs.Definitions

@[expose] public section

namespace Erdos878

open scoped BigOperators

/-- The largest power of `p` no greater than `n`. -/
noncomputable def primePower (p n : ℕ) : ℕ := p ^ Nat.log p n

private theorem primePower_properties {p n : ℕ} (hp : p ∈ n.primeFactors) :
    2 ≤ primePower p n ∧ primePower p n ≤ n ∧ (primePower p n).primeFactors = {p} := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hnz := (Nat.mem_primeFactors.mp hp).2.2
  have hlog := Nat.log_pos hprime.one_lt (Nat.le_of_mem_primeFactors hp)
  refine ⟨hprime.two_le.trans (Nat.le_self_pow hlog.ne' p), Nat.pow_log_le_self p hnz, ?_⟩
  exact Nat.primeFactors_prime_pow hlog.ne' hprime

/-- Sum admissible terms from an indexed family with disjoint prime supports. -/
theorem sum_le_F_of_disjoint {ι : Type*} (n : ℕ) (s : Finset ι) (g : ι → ℕ)
    (hlo : ∀ i ∈ s, 2 ≤ g i) (hhi : ∀ i ∈ s, g i ≤ n)
    (hsupp : ∀ i ∈ s, (g i).primeFactors ⊆ n.primeFactors)
    (hdisj : Set.PairwiseDisjoint (↑s) (fun i ↦ (g i).primeFactors)) :
    ∑ i ∈ s, g i ≤ F n := by
  classical
  have hcop {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j) :
      (g i).Coprime (g j) :=
    (Nat.disjoint_primeFactors (by have := hlo i hi; omega)
      (by have := hlo j hj; omega)).mp (hdisj hi hj hne)
  have hinj : Set.InjOn g ↑s := by
    intro i hi j hj heq
    by_contra hne
    have h := hcop hi hj hne
    rw [heq, Nat.coprime_self] at h
    have := hlo j hj
    omega
  calc
    ∑ i ∈ s, g i = ∑ a ∈ s.image g, a := by
      simpa only [id_eq] using (Finset.sum_image (f := id) hinj).symm
    _ ≤ F n := by
      unfold F
      apply Finset.le_sup (f := fun A : Finset ℕ ↦ ∑ a ∈ A, a)
      have hsubset : s.image g ⊆ Finset.Icc 2 n := by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_Icc.mpr ⟨hlo i hi, hhi i hi⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsubset, hsubset, ?_, ?_⟩
      · intro a ha b hb hab
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
        exact hcop hi hj (fun h ↦ hab (congrArg g h))
      · intro a ha p hp hpa
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact Nat.dvd_of_mem_primeFactors
          (hsupp i hi (hp.mem_primeFactors hpa (by have := hlo i hi; omega)))

theorem f_le_F (n : ℕ) : f n ≤ F n := by
  classical
  change (∑ p ∈ n.primeFactors, primePower p n) ≤ F n
  apply sum_le_F_of_disjoint n n.primeFactors (fun p ↦ primePower p n)
  · exact fun _ hp ↦ (primePower_properties hp).1
  · exact fun _ hp ↦ (primePower_properties hp).2.1
  · intro p hp
    rw [(primePower_properties hp).2.2]
    exact Finset.singleton_subset_iff.mpr hp
  · intro p hp q hq hpq
    change Disjoint (primePower p n).primeFactors (primePower q n).primeFactors
    rw [(primePower_properties hp).2.2, (primePower_properties hq).2.2]
    simp [hpq]

/-- The term `a` improves the prime-power sum precisely when replacing its support yields a gain. -/
theorem equality_iff_no_improvement (n : ℕ) : f n = F n ↔
    ∀ a : ℕ, 2 ≤ a → a ≤ n → a.primeFactors ⊆ n.primeFactors →
      a ≤ ∑ p ∈ a.primeFactors, primePower p n := by
  classical
  constructor
  · intro heq a ha hax hs
    let s := n.primeFactors \ a.primeFactors
    let g : ℕ → ℕ := fun p ↦ if p = 0 then a else primePower p n
    have hprops : ∀ i ∈ s, 2 ≤ g i ∧ g i ≤ n ∧ (g i).primeFactors = {i} := by
      intro i hi
      have hin : i ∈ n.primeFactors := (Finset.mem_sdiff.mp hi).1
      have hinz := (Nat.prime_of_mem_primeFactors hin).ne_zero
      simpa [g, hinz] using primePower_properties hin
    have hg0 : g 0 = a := by simp [g]
    have h0 : 0 ∉ s := by
      intro hz
      exact (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hz).1).ne_zero rfl
    have hsum := sum_le_F_of_disjoint n (insert 0 s) g
      (fun i hi ↦ (Finset.mem_insert.mp hi).elim (fun h ↦ by simpa [h, hg0] using ha)
        (fun h ↦ (hprops i h).1))
      (fun i hi ↦ (Finset.mem_insert.mp hi).elim (fun h ↦ by simpa [h, hg0] using hax)
        (fun h ↦ (hprops i h).2.1))
      (fun i hi ↦ (Finset.mem_insert.mp hi).elim (fun h ↦ by simpa [h, hg0] using hs)
        (fun h ↦ by
          rw [(hprops i h).2.2]
          exact Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp h).1))
      (by
        intro i hi j hj hij
        change Disjoint (g i).primeFactors (g j).primeFactors
        rcases Finset.mem_insert.mp hi with rfl | hi
        · have hj' := (Finset.mem_insert.mp hj).resolve_left (Ne.symm hij)
          rw [hg0, (hprops j hj').2.2]
          exact Finset.disjoint_singleton_right.mpr (Finset.mem_sdiff.mp hj').2
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · rw [hg0, (hprops i hi).2.2]
            exact Finset.disjoint_singleton_left.mpr (Finset.mem_sdiff.mp hi).2
          · rw [(hprops i hi).2.2, (hprops j hj).2.2]
            simp [hij])
    rw [Finset.sum_insert h0, hg0, ← heq] at hsum
    have hgs : ∑ i ∈ s, g i = ∑ i ∈ s, primePower i n := by
      apply Finset.sum_congr rfl
      intro i hi
      have hinz := (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hi).1).ne_zero
      simp [g, hinz]
    rw [hgs] at hsum
    change a + (∑ i ∈ s, primePower i n) ≤ ∑ p ∈ n.primeFactors, primePower p n at hsum
    have hadd := Finset.sum_sdiff (f := fun p ↦ primePower p n) hs
    change (∑ i ∈ s, primePower i n) + (∑ p ∈ a.primeFactors, primePower p n) =
      ∑ p ∈ n.primeFactors, primePower p n at hadd
    omega
  · intro h
    apply le_antisymm (f_le_F n)
    unfold F
    apply Finset.sup_le
    intro A hA
    obtain ⟨_, hsub, hpair, hprime⟩ := Finset.mem_filter.mp hA
    have hloc (a : ℕ) (ha : a ∈ A) : a.primeFactors ⊆ n.primeFactors := by
      intro p hp
      have hnz : n ≠ 0 := by have := Finset.mem_Icc.mp (hsub ha); omega
      exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
        (hprime a ha p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)) hnz
    have hdisj : Set.PairwiseDisjoint (↑A) Nat.primeFactors := by
      intro a ha b hb hab
      exact Nat.Coprime.disjoint_primeFactors (hpair ha hb hab)
    calc
      ∑ a ∈ A, a ≤ ∑ a ∈ A, ∑ p ∈ a.primeFactors, primePower p n := by
        apply Finset.sum_le_sum
        intro a ha
        have hb := Finset.mem_Icc.mp (hsub ha)
        exact h a hb.1 hb.2 (hloc a ha)
      _ = ∑ p ∈ A.biUnion Nat.primeFactors, primePower p n := (Finset.sum_biUnion hdisj).symm
      _ ≤ f n := by
        apply Finset.sum_le_sum_of_subset
        intro p hp
        obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp hp
        exact hloc a ha hpa

/-- The fixed prime factors of the cofactor and the one variable base. -/
abbrev CofactorIndex (m : ℕ) := Option {p : ℕ // p ∈ m.primeFactors}

/-- The real bases used to test candidate summands. -/
def cofactorBase (m : ℕ) (u : ℝ) : CofactorIndex m → ℝ
  | none => u
  | some p => p.val

/-- The exponents needed by every summand no greater than `x`. -/
abbrev CofactorExponents (x m : ℕ) := CofactorIndex m → Fin (Nat.log 2 x + 1)

/-- A candidate product of the fixed bases and the variable base. -/
noncomputable def cofactorValue (x m : ℕ) (u : ℝ) (a : CofactorExponents x m) : ℝ :=
  ∏ i, cofactorBase m u i ^ (a i).val

/-- The largest permitted exponent for base `b` at the real endpoint `N`. -/
noncomputable def realPrimeExponent (x : ℕ) (b N : ℝ) : ℕ :=
  ((Finset.range (Nat.log 2 x + 1)).filter fun k ↦ b ^ k ≤ N).sup id

/-- A real value `u` passes the cofactor comparison when no mixed product improves its support. -/
noncomputable def cofactorGood (x m : ℕ) (u : ℝ) : Prop :=
  ∀ a : CofactorExponents x m, 2 ≤ cofactorValue x m u a →
    cofactorValue x m u a ≤ (m : ℝ) * u →
    cofactorValue x m u a ≤
      ∑ i, if (a i).val = 0 then 0 else
        cofactorBase m u i ^ realPrimeExponent x (cofactorBase m u i) ((m : ℝ) * u)

private def natCofactorBase (m p : ℕ) : CofactorIndex m → ℕ
  | none => p
  | some q => q.val

private theorem natCofactorBase_prime {m p : ℕ} (hp : p.Prime) (i : CofactorIndex m) :
    (natCofactorBase m p i).Prime := by
  cases i with
  | none => exact hp
  | some q => exact Nat.prime_of_mem_primeFactors q.property

private theorem natCofactorBase_injective {m p : ℕ} (hp : p ∉ m.primeFactors) :
    Function.Injective (natCofactorBase m p) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some q =>
      change p = q.val at hij
      exact False.elim (hp (hij.symm ▸ q.property))
  | some q =>
    cases j with
    | none =>
      change q.val = p at hij
      exact False.elim (hp (hij ▸ q.property))
    | some r => exact congrArg some (Subtype.ext hij)

private theorem image_natCofactorBase {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) :
    Finset.univ.image (natCofactorBase m p) = (m * p).primeFactors := by
  rw [Nat.primeFactors_mul hm hp.ne_zero, hp.primeFactors]
  ext q
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | none => exact Or.inr rfl
    | some r => exact Or.inl r.property
  · rintro (hq | rfl)
    · exact ⟨some ⟨q, hq⟩, rfl⟩
    · exact ⟨none, rfl⟩

private theorem cast_natCofactorBase (m p : ℕ) (i : CofactorIndex m) :
    (natCofactorBase m p i : ℝ) = cofactorBase m p i := by
  cases i <;> rfl

private theorem log_le_log_two {p n x : ℕ} (hp : 2 ≤ p) (hn : n ≠ 0) (hnx : n ≤ x) :
    Nat.log p n ≤ Nat.log 2 x :=
  Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_left hp _).trans
    ((Nat.pow_log_le_self p hn).trans hnx))

private theorem realPrimeExponent_cast {x b n : ℕ} (hb : 2 ≤ b) (hn : n ≠ 0) (hnx : n ≤ x) :
    realPrimeExponent x b n = Nat.log b n := by
  unfold realPrimeExponent
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    have h := (Finset.mem_filter.mp ha).2
    exact Nat.le_log_of_pow_le (by omega) (by exact_mod_cast h)
  · apply Finset.le_sup (f := id)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (log_le_log_two hb hn hnx)),
      by exact_mod_cast Nat.pow_log_le_self b hn⟩

private theorem primeFactors_prod_powers {ι : Type*} [Fintype ι]
    (b a : ι → ℕ) (hb : ∀ i, (b i).Prime) :
    (∏ i, b i ^ a i).primeFactors = (Finset.univ.filter fun i ↦ a i ≠ 0).image b := by
  classical
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff,
    Nat.factorization_prod_apply (fun i _ ↦ pow_ne_zero _ (hb i).ne_zero)]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    apply h
    apply Finset.sum_eq_zero
    intro i _
    rw [(hb i).factorization_pow, Finsupp.single_apply]
    split_ifs with hbp
    · by_contra hai
      exact hn ⟨i, hai, by simpa only [eq_comm] using hbp⟩
    · rfl
  · rintro ⟨i, hi, rfl⟩ hn
    have hle := Finset.single_le_sum
      (f := fun j ↦ (b j ^ a j).factorization (b i))
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [Nat.factorization_pow_self (hb i), hn] at hle
    omega

private noncomputable def natCofactorValue (x m p : ℕ) (a : CofactorExponents x m) : ℕ :=
  ∏ i, natCofactorBase m p i ^ (a i).val

private theorem cast_natCofactorValue (x m p : ℕ) (a : CofactorExponents x m) :
    (natCofactorValue x m p a : ℝ) = cofactorValue x m (p : ℝ) a := by
  simp only [natCofactorValue, cofactorValue, Nat.cast_prod, Nat.cast_pow, cast_natCofactorBase]

private theorem natCofactorValue_support {x m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (a : CofactorExponents x m) :
    (natCofactorValue x m p a).primeFactors ⊆ (m * p).primeFactors := by
  rw [natCofactorValue, primeFactors_prod_powers _ _ (natCofactorBase_prime hp),
    ← image_natCofactorBase hm hp]
  exact Finset.image_mono _ (Finset.filter_subset _ _)

private theorem cofactorSum_eq_cast {x m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hpm : p ∉ m.primeFactors) (hxp : m * p ≤ x) (a : CofactorExponents x m) :
    (∑ i, if (a i).val = 0 then 0 else cofactorBase m (p : ℝ) i ^
      realPrimeExponent x (cofactorBase m (p : ℝ) i) ((m : ℝ) * p)) =
    ((∑ q ∈ (natCofactorValue x m p a).primeFactors, primePower q (m * p)) : ℝ) := by
  classical
  rw [natCofactorValue, primeFactors_prod_powers _ _ (natCofactorBase_prime hp),
    Finset.sum_image (natCofactorBase_injective hpm).injOn, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : (a i).val = 0
  · simp [ha]
  · simp only [ha, ite_false, ite_true, ne_eq, not_false_eq_true]
    rw [← cast_natCofactorBase, ← Nat.cast_mul,
      realPrimeExponent_cast (natCofactorBase_prime hp i).two_le
        (Nat.mul_ne_zero hm hp.ne_zero) hxp]
    simp [primePower]

private theorem exists_natCofactorValue {x m p A : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hpm : p ∉ m.primeFactors) (hA : A ≠ 0) (hAx : A ≤ x)
    (hs : A.primeFactors ⊆ (m * p).primeFactors) :
    ∃ a : CofactorExponents x m, natCofactorValue x m p a = A := by
  classical
  let b := natCofactorBase m p
  let a : CofactorExponents x m := fun i ↦ ⟨A.factorization (b i), by
    apply Nat.lt_succ_of_le
    apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    exact (Nat.pow_le_pow_left (natCofactorBase_prime hp i).two_le _).trans
      ((Nat.ordProj_le (b i) hA).trans hAx)⟩
  refine ⟨a, ?_⟩
  change (∏ i, b i ^ A.factorization (b i)) = A
  calc
    _ = ∏ q ∈ Finset.univ.image b, q ^ A.factorization q := by
      symm
      exact Finset.prod_image (natCofactorBase_injective hpm).injOn
    _ = ∏ q ∈ A.primeFactors, q ^ A.factorization q := by
      rw [image_natCofactorBase hm hp]
      symm
      apply Finset.prod_subset hs
      intro q _ hq
      have hz : A.factorization q = 0 := by
        apply Finsupp.notMem_support_iff.mp
        simpa only [Nat.support_factorization] using hq
      simp [hz]
    _ = A := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors (· ^ ·),
        Nat.prod_factorization_pow_eq_self hA]

/-- At an admissible prime variable, the real cofactor test is exactly the original equality. -/
theorem cofactorGood_prime_iff {x m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hpm : p ∉ m.primeFactors) (hxp : m * p ≤ x) :
    cofactorGood x m (p : ℝ) ↔ f (m * p) = F (m * p) := by
  rw [equality_iff_no_improvement]
  constructor
  · intro h A ha haN hs
    obtain ⟨a, hA⟩ := exists_natCofactorValue hm hp hpm (by omega) (haN.trans hxp) hs
    have hrA : cofactorValue x m (p : ℝ) a = (A : ℝ) := by
      rw [← cast_natCofactorValue, hA]
    have hr2 : 2 ≤ cofactorValue x m (p : ℝ) a := by
      rw [hrA]
      exact_mod_cast ha
    have hrN : cofactorValue x m (p : ℝ) a ≤ (m : ℝ) * p := by
      rw [hrA]
      exact_mod_cast haN
    have ho := h a hr2 hrN
    rw [hrA, cofactorSum_eq_cast hm hp hpm hxp, hA] at ho
    exact_mod_cast ho
  · intro h a ha haN
    rw [← cast_natCofactorValue] at ha haN ⊢
    rw [cofactorSum_eq_cast hm hp hpm hxp]
    exact_mod_cast h _ (by exact_mod_cast ha) (by exact_mod_cast haN)
      (natCofactorValue_support hm hp a)

end Erdos878
