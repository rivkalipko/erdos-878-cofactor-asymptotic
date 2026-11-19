module

public import Erdos878Proofs.CofactorExceptions
public import Erdos878Proofs.CofactorGlobalError
public import Erdos878Proofs.CofactorDenominator

@[expose] public section

/-! # An asymptotic equivalent for the equality count in part (iv) -/

open Filter Asymptotics

namespace Erdos878

private noncomputable def retainedCount (x : ℕ) : ℝ :=
  (retainedEqualities x (omegaCutoff x) (cofactorThreshold x)).card

private lemma discard_error : (E - retainedCount) =o[atTop] (fun x : ℕ ↦ (x : ℝ) / Real.log x) := by
  apply IsBigO.trans_isLittleO _ ((discardSmooth_isLittleO.add discardLargeSquares_isLittleO).add
    discardManyPrimeFactors_isLittleO)
  apply isBigO_of_le
  intro x
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  exact (abs_E_sub_retained_le x).trans (le_abs_self _)

/-- Part (iv) of Erdős Problem 878. The equality count is asymptotic to a sum of
logarithmic integrals over explicitly defined real sets indexed by cofactors. -/
theorem part_iv : E ~[atTop] cofactorAnswer := by
  have hcount : retainedCount = cofactorPrimeSum := by
    funext x
    simp only [retainedCount, cofactorPrimeSum, card_retainedEqualities, Nat.cast_sum]
  have hretained : (retainedCount - cofactorAnswer) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log x) := by
    rw [hcount]
    exact cofactor_primes_sub_answer_isLittleO
  exact E_isEquivalent_of_error (discard_error.triangle hretained)

end Erdos878
