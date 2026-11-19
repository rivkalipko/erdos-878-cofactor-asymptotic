module

public import Erdos878Proofs.CofactorIntervals

@[expose] public section

/-! # Largest-prime decomposition for the equality count -/

namespace Erdos878

open scoped BigOperators Classical

/-- The least allowed real value of the variable prime. -/
noncomputable def cofactorLower (m : ℕ) (Y : ℝ) : ℝ :=
  max Y ((m.primeFactors.sup id : ℕ) : ℝ)

/-- The upper endpoint of the variable prime. -/
noncomputable def cofactorUpper (x m : ℕ) : ℝ := (x : ℝ) / m

/-- Cofactors which meet the size and prime-factor cutoffs. -/
noncomputable def cofactorIndices (x K : ℕ) (Y : ℝ) : Finset ℕ :=
  (Finset.Ico 1 x).filter fun m ↦ m.primeFactors.card ≤ K ∧ Y < cofactorUpper x m

/-- The primes producing an equality integer with a given cofactor. -/
noncomputable def cofactorPrimes (x m : ℕ) (Y : ℝ) : Finset ℕ :=
  x.primesBelow.filter fun p ↦
    (p : ℝ) ∈ Set.Ioo (cofactorLower m Y) (cofactorUpper x m) ∧ cofactorGood x m p

/-- Equality integers whose largest prime exceeds `Y` and occurs to the first power,
with at most `K` other distinct prime factors. -/
noncomputable def retainedEqualities (x K : ℕ) (Y : ℝ) : Finset ℕ :=
  (Finset.Ico 1 x).filter fun n ↦
    f n = F n ∧ n.primeFactors.card ≤ K + 1 ∧
      ∃ p ∈ n.primeFactors, Y < (p : ℝ) ∧
        (∀ q ∈ n.primeFactors, q ≤ p) ∧ ¬p ^ 2 ∣ n

private theorem primeFactors_mul_prime {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) :
    (m * p).primeFactors = insert p m.primeFactors := by
  rw [Nat.mul_comm, Nat.primeFactors_mul hp.ne_zero hm, hp.primeFactors, Finset.singleton_union]

private theorem lt_of_cofactorLower_lt {m p : ℕ} {Y : ℝ}
    (h : cofactorLower m Y < (p : ℝ)) (q : ℕ) (hq : q ∈ m.primeFactors) : q < p := by
  have hsup : q ≤ m.primeFactors.sup id := Finset.le_sup (f := id) hq
  have hp : ((m.primeFactors.sup id : ℕ) : ℝ) < p := (le_max_right Y _).trans_lt h
  exact hsup.trans_lt (by exact_mod_cast hp)

private theorem cofactorLower_lt_of_all_lt {m p : ℕ} {Y : ℝ}
    (hp : 0 < p) (hY : Y < (p : ℝ)) (hq : ∀ q ∈ m.primeFactors, q < p) :
    cofactorLower m Y < (p : ℝ) := by
  have hsup : m.primeFactors.sup id ≤ p - 1 := by
    apply Finset.sup_le
    intro q hqm
    have := hq q hqm
    simpa only [id_eq] using (show q ≤ p - 1 by omega)
  have hlt : m.primeFactors.sup id < p := by omega
  exact max_lt_iff.mpr ⟨hY, by exact_mod_cast hlt⟩

private theorem cofactor_product_mem_retained {x K m p : ℕ} {Y : ℝ}
    (hmidx : m ∈ cofactorIndices x K Y) (hpp : p ∈ cofactorPrimes x m Y) :
    m * p ∈ retainedEqualities x K Y := by
  obtain ⟨hmx, hmcard, _⟩ := Finset.mem_filter.mp hmidx
  obtain ⟨hp', hinterval, hgood⟩ := Finset.mem_filter.mp hpp
  have hp := (Nat.mem_primesBelow.mp hp').2
  have hm : 0 < m := (Finset.mem_Ico.mp hmx).1
  have hltall := lt_of_cofactorLower_lt hinterval.1
  have hpn : p ∉ m.primeFactors := fun h ↦ (lt_irrefl p) (hltall _ h)
  have hmp : m * p < x := by
    have hlt := (lt_div_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)).mp hinterval.2
    rw [mul_comm] at hlt
    exact_mod_cast hlt
  have hfac := primeFactors_mul_prime hm.ne' hp
  have hcard : (m * p).primeFactors.card ≤ K + 1 := by
    rw [hfac, Finset.card_insert_of_notMem hpn]
    omega
  have hsquare : ¬p ^ 2 ∣ m * p := by
    intro hd
    have hd' : p * p ∣ p * m := by simpa only [pow_two, Nat.mul_comm m p] using hd
    exact hpn (hp.mem_primeFactors (Nat.dvd_of_mul_dvd_mul_left hp.pos hd') hm.ne')
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ico.mpr ⟨Nat.mul_pos hm hp.pos, hmp⟩,
    (cofactorGood_prime_iff hm.ne' hp hpn hmp.le).mp hgood, hcard, p, ?_,
      (le_max_left Y _).trans_lt hinterval.1, ?_, hsquare⟩
  · simp [hfac]
  · intro q hq
    rw [hfac] at hq
    exact (Finset.mem_insert.mp hq).elim (fun heq ↦ heq.le) (fun hn ↦ (hltall q hn).le)

private theorem exists_cofactor_of_mem_retained {x K n : ℕ} {Y : ℝ}
    (hn : n ∈ retainedEqualities x K Y) :
    ∃ m ∈ cofactorIndices x K Y, ∃ p ∈ cofactorPrimes x m Y, m * p = n := by
  obtain ⟨hnrange, heq, hcard, p, hpF, hY, hmax, hsq⟩ := Finset.mem_filter.mp hn
  have hp := Nat.prime_of_mem_primeFactors hpF
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mem_primeFactors hpF
  have hm : 0 < m := by
    by_contra! hm0
    have := (Finset.mem_Ico.mp hnrange).1
    have hh : m = 0 := by omega
    simp [hh] at this
  have hmp : m * p < x := by simpa only [Nat.mul_comm] using (Finset.mem_Ico.mp hnrange).2
  have hfat : (p * m).primeFactors = insert p m.primeFactors := by
    simpa only [Nat.mul_comm] using primeFactors_mul_prime hm.ne' hp
  have hpn : p ∉ m.primeFactors := by
    intro hpm
    apply hsq
    obtain ⟨j, hj⟩ := Nat.dvd_of_mem_primeFactors hpm
    exact ⟨j, by rw [hj]; ring⟩
  have hq : ∀ q ∈ m.primeFactors, q < p := by
    intro q hq
    have hqle := hmax q (by rw [hfat]; exact Finset.mem_insert_of_mem hq)
    exact lt_of_le_of_ne hqle (fun heq ↦ hpn (heq ▸ hq))
  have hcm : m.primeFactors.card ≤ K := by
    rw [hfat, Finset.card_insert_of_notMem hpn] at hcard
    omega
  have hm_lt : m < x := (Nat.le_mul_of_pos_right m hp.pos).trans_lt hmp
  have hp_lt : p < x := (Nat.le_mul_of_pos_left p hm).trans_lt hmp
  have hupper : (p : ℝ) < cofactorUpper x m := by
    apply (lt_div_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)).mpr
    rw [mul_comm]
    exact_mod_cast hmp
  refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hm, hm_lt⟩, hcm, hY.trans hupper⟩,
    p, Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨hp_lt, hp⟩,
      ⟨cofactorLower_lt_of_all_lt hp.pos hY hq, hupper⟩, ?_⟩, Nat.mul_comm _ _⟩
  apply (cofactorGood_prime_iff hm.ne' hp hpn hmp.le).mpr
  simpa only [Nat.mul_comm] using heq

private theorem primeFactors_sup_cofactor {x m p : ℕ} {Y : ℝ}
    (hm : m ≠ 0) (hp : p ∈ cofactorPrimes x m Y) : (m * p).primeFactors.sup id = p := by
  obtain ⟨hp', hI, _⟩ := Finset.mem_filter.mp hp
  rw [primeFactors_mul_prime hm (Nat.mem_primesBelow.mp hp').2]
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    exact (Finset.mem_insert.mp hq).elim (fun h ↦ h.le)
      (fun h ↦ (lt_of_cofactorLower_lt hI.1 q h).le)
  · exact Finset.le_sup (f := id) (Finset.mem_insert_self _ _)

/-- The retained equality count is a sum over cofactors of prime counts in their real intervals. -/
theorem card_retainedEqualities (x K : ℕ) (Y : ℝ) :
    (retainedEqualities x K Y).card =
      ∑ m ∈ cofactorIndices x K Y, (cofactorPrimes x m Y).card := by
  let s := (cofactorIndices x K Y).sigma (fun m ↦ cofactorPrimes x m Y)
  let g : (Σ _ : ℕ, ℕ) → ℕ := fun mp ↦ mp.1 * mp.2
  have himage : s.image g = retainedEqualities x K Y := by
    ext n
    constructor
    · intro hn
      obtain ⟨⟨m, p⟩, hmp, rfl⟩ := Finset.mem_image.mp hn
      exact cofactor_product_mem_retained (Finset.mem_sigma.mp hmp).1 (Finset.mem_sigma.mp hmp).2
    · intro hn
      obtain ⟨m, hm, p, hp, h⟩ := exists_cofactor_of_mem_retained hn
      exact Finset.mem_image.mpr ⟨⟨m, p⟩, Finset.mem_sigma.mpr ⟨hm, hp⟩, h⟩
  have hinj : Set.InjOn g ↑s := by
    rintro ⟨m, p⟩ hmp ⟨m', p'⟩ hmp' heq
    obtain ⟨hm, hp⟩ := Finset.mem_sigma.mp hmp
    obtain ⟨hm', hp'⟩ := Finset.mem_sigma.mp hmp'
    change m ∈ cofactorIndices x K Y at hm
    change m' ∈ cofactorIndices x K Y at hm'
    change p ∈ cofactorPrimes x m Y at hp
    change p' ∈ cofactorPrimes x m' Y at hp'
    have hm0 : m ≠ 0 := by
      have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1
      omega
    have hm0' : m' ≠ 0 := by
      have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hm').1).1
      omega
    change m * p = m' * p' at heq
    have hpp' := congrArg (fun j : ℕ ↦ j.primeFactors.sup id) heq
    rw [primeFactors_sup_cofactor hm0 hp, primeFactors_sup_cofactor hm0' hp'] at hpp'
    subst p'
    have hpos := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2.pos
    have hmm' := Nat.eq_of_mul_eq_mul_right hpos heq
    subst m'
    rfl
  rw [← himage, Finset.card_image_of_injOn hinj, Finset.card_sigma]

/-- A prime is an equality integer. -/
theorem equality_at_prime {p : ℕ} (hp : p.Prime) : f p = F p := by
  apply (equality_iff_no_improvement p).mpr
  intro a ha hap hs
  obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < a)
  have hqp := hs hq
  rw [hp.primeFactors, Finset.mem_singleton] at hqp
  subst q
  have hpa := Nat.le_of_dvd (by omega : 0 < a) (Nat.dvd_of_mem_primeFactors hq)
  have hpa' : a = p := le_antisymm hap hpa
  subst a
  rw [hp.primeFactors, Finset.sum_singleton]
  exact Nat.le_self_pow (Nat.log_pos hp.one_lt le_rfl).ne' p

/-- The number of primes below `x` is a lower bound for the equality count. -/
theorem card_primesBelow_le_E (x : ℕ) : (x.primesBelow.card : ℝ) ≤ E x := by
  have hs : x.primesBelow ⊆ (Finset.Ico 1 x).filter fun n ↦ f n = F n := by
    intro p h
    obtain ⟨hpx, hp⟩ := Nat.mem_primesBelow.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hp.one_le, hpx⟩, equality_at_prime hp⟩
  unfold E
  exact_mod_cast Finset.card_le_card hs

end Erdos878
