module

public import Erdos878Proofs.EAsymptotic

/-! # Verified solution for part (iv) of Erdős Problem 878 -/

@[expose] public section

open Filter Asymptotics

namespace Erdos878

/-- The explicit sum of logarithmic integrals for the equality count. -/
noncomputable def erdos_878.parts.iv.answer : ℕ → ℝ := cofactorAnswer

/-- The number of positive integers `n < x` with `f n = F n` is asymptotic
to the explicit sum of logarithmic integrals. -/
theorem erdos_878.parts.iv :
    (fun x : ℕ ↦ (((Finset.Ico 1 x).filter fun n ↦ f n = F n).card : ℝ))
      ~[atTop] erdos_878.parts.iv.answer := part_iv

end Erdos878

#print axioms Erdos878.erdos_878.parts.iv
