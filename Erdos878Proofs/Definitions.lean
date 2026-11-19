module

public import Mathlib

@[expose] public section

namespace Erdos878

noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

open scoped Classical in
noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).powerset.filter fun A ↦
    A ⊆ Finset.Icc 2 n ∧
      (A : Set ℕ).Pairwise (fun a b ↦ Nat.Coprime a b) ∧
      ∀ a ∈ A, ∀ p, p.Prime → p ∣ a → p ∣ n).sup fun A ↦ ∑ a ∈ A, a

noncomputable def E (x : ℕ) : ℝ :=
  ((Finset.Ico 1 x).filter fun n ↦ f n = F n).card

/-- The threshold for the largest prime in the cofactor decomposition. -/
noncomputable def cofactorThreshold (x : ℕ) : ℝ :=
  Real.exp (Real.log (x : ℝ) ^ (2 / 3 : ℝ))

/-- The maximum number of distinct prime factors allowed in the cofactor. -/
noncomputable def omegaCutoff (x : ℕ) : ℕ :=
  ⌊Real.log (x : ℝ) ^ (1 / 20 : ℝ)⌋₊

noncomputable def manyPrimeFactors (x : ℕ) : Finset ℕ :=
  (Finset.Ico 1 x).filter (fun n ↦ omegaCutoff x < n.primeFactors.card)

noncomputable def largeSquareDivisor (x : ℕ) : Finset ℕ :=
  (Finset.Ico 1 x).filter fun n ↦
    ∃ d ∈ Finset.Icc 1 x, cofactorThreshold x < (d : ℝ) ∧ d ^ 2 ∣ n

def primeBases (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

end Erdos878
