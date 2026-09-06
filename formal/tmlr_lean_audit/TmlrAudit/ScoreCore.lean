import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Card

namespace TmlrAudit

open scoped BigOperators

/-- The exponential sum whose ordering is the ordering of the true-label softmax loss. -/
def otherExpSum {K : ℕ} (z : Fin K → ℝ) (y : Fin K) (β : ℝ) : ℝ :=
  ∑ a ∈ (Finset.univ.erase y), Real.exp (β * (z a - z y))

/-- Every observation has the same exponential sum `K-1` at inverse temperature zero. -/
lemma otherExpSum_zero {K : ℕ} (z : Fin K → ℝ) (y : Fin K) :
    otherExpSum z y 0 = K - 1 := by
  simp [otherExpSum, Finset.card_erase_of_mem]

/-- Hence every pair-difference has the root `β = 0`. -/
lemma pairDifference_zero {K : ℕ}
    (z₁ z₂ : Fin K → ℝ) (y₁ y₂ : Fin K) :
    otherExpSum z₁ y₁ 0 - otherExpSum z₂ y₂ 0 = 0 := by
  simp [otherExpSum_zero]

end TmlrAudit
