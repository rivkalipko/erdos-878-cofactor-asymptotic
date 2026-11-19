/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Erdős Problem 878, part (iv)

The definitions of `f` and `F` come from the Apache-2.0-licensed statement
`FormalConjectures/ErdosProblems/878.lean`.
-/

@[expose] public section

open Filter Asymptotics MeasureTheory Real
open scoped BigOperators

noncomputable section

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

/-- The least allowed real value of the variable prime. -/
noncomputable def cofactorLower (m : ℕ) (Y : ℝ) : ℝ :=
  max Y ((m.primeFactors.sup id : ℕ) : ℝ)

/-- The upper endpoint of the variable prime. -/
noncomputable def cofactorUpper (x m : ℕ) : ℝ := (x : ℝ) / m

/-- Cofactors which meet the size and prime-factor cutoffs. -/
noncomputable def cofactorIndices (x K : ℕ) (Y : ℝ) : Finset ℕ :=
  (Finset.Ico 1 x).filter fun m ↦ m.primeFactors.card ≤ K ∧ Y < cofactorUpper x m

/-- The logarithmic integral over the part of the interval passing the cofactor test. -/
def cofactorIntegral (x m : ℕ) (l r : ℝ) : ℝ :=
  ∫ u in {u | u ∈ Set.Ioo l r ∧ cofactorGood x m u}, (log u)⁻¹

/-- The finite sum of logarithmic integrals in the answer to part (iv). -/
noncomputable def cofactorAnswer (x : ℕ) : ℝ :=
  ∑ m ∈ cofactorIndices x (omegaCutoff x) (cofactorThreshold x),
    cofactorIntegral x m (cofactorLower m (cofactorThreshold x)) (cofactorUpper x m)

/-- The explicit sum of logarithmic integrals for the equality count. -/
noncomputable def erdos_878.parts.iv.answer : ℕ → ℝ := cofactorAnswer

/-- The number of positive integers `n < x` with `f n = F n` is asymptotic
to the explicit sum of logarithmic integrals. -/
theorem erdos_878.parts.iv :
    (fun x : ℕ ↦ (((Finset.Ico 1 x).filter fun n ↦ f n = F n).card : ℝ))
      ~[atTop] erdos_878.parts.iv.answer := by
  sorry

end Erdos878
