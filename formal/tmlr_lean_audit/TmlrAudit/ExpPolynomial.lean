import TmlrAudit.RolleCore
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace TmlrAudit

open scoped BigOperators
noncomputable section

/-- A finite real exponential sum indexed by a finset. -/
def expSum {α : Type*} [DecidableEq α] (I : Finset α)
    (c λ : α → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ I, c i * Real.exp (λ i * x)

/-- Derivative of a finite exponential sum. -/
lemma hasDerivAt_expSum {α : Type*} [DecidableEq α]
    (I : Finset α) (c λ : α → ℝ) (x : ℝ) :
    HasDerivAt (expSum I c λ)
      (∑ i ∈ I, c i * λ i * Real.exp (λ i * x)) x := by
  unfold expSum
  convert HasDerivAt.fun_sum (u := I) (x := x) (fun i _hi =>
    HasDerivAt.const_mul (c i)
      ((Real.hasDerivAt_exp (λ i * x)).comp x (hasDerivAt_const_mul (λ i)))) using 1
  ring

lemma continuous_expSum {α : Type*} [DecidableEq α]
    (I : Finset α) (c λ : α → ℝ) :
    Continuous (expSum I c λ) := by
  fun_prop

/-- Normalize an exponential sum by one distinguished exponent. -/
def normalizedExpSum {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (c λ : α → ℝ) (x : ℝ) : ℝ :=
  c a + ∑ i ∈ s, c i * Real.exp ((λ i - λ a) * x)

lemma normalizedExpSum_eq_factor {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (ha : a ∉ s) (c λ : α → ℝ) (x : ℝ) :
    normalizedExpSum a s c λ x =
      Real.exp (-λ a * x) * expSum (insert a s) c λ x := by
  classical
  simp only [normalizedExpSum, expSum, Finset.sum_insert, ha, not_false_eq_true]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · rw [← Real.exp_add]
    ring_nf
    simp
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.exp_add]
    ring_nf
    simp [mul_assoc, mul_left_comm, mul_comm]

lemma normalizedExpSum_zero_iff {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (ha : a ∉ s) (c λ : α → ℝ) (x : ℝ) :
    normalizedExpSum a s c λ x = 0 ↔ expSum (insert a s) c λ x = 0 := by
  rw [normalizedExpSum_eq_factor a s ha c λ x, mul_eq_zero]
  simp

/-- The derivative of the normalized sum has one fewer exponential term. -/
lemma hasDerivAt_normalizedExpSum {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (c λ : α → ℝ) (x : ℝ) :
    HasDerivAt (normalizedExpSum a s c λ)
      (expSum s (fun i => c i * (λ i - λ a)) (fun i => λ i - λ a) x) x := by
  unfold normalizedExpSum expSum
  convert (hasDerivAt_const x (c a)).add
    (HasDerivAt.fun_sum (u := s) (x := x) (fun i _hi =>
      HasDerivAt.const_mul (c i)
        ((Real.hasDerivAt_exp ((λ i - λ a) * x)).comp x
          (hasDerivAt_const_mul (λ i - λ a))))) using 1 <;>
  ring

/-- A nonzero finite sum of exponentials with distinct exponents has at most one fewer
real zero than the number of terms. This is the manuscript's Lemma A.1 in finite-set form. -/
theorem expSum_zero_set_finite_and_ncard_le {α : Type*} [DecidableEq α]
    (I : Finset α) (hI : I.Nonempty) (c λ : α → ℝ)
    (hc : ∀ i ∈ I, c i ≠ 0)
    (hλ : Set.InjOn λ (I : Set α)) :
    {x | expSum I c λ x = 0}.Finite ∧
      Set.ncard {x | expSum I c λ x = 0} ≤ I.card - 1 := by
  induction I using Finset.induction_on generalizing c λ with
  | empty => simp at hI
  | @insert a s ha ih =>
      by_cases hs : s.Nonempty
      · let c' : α → ℝ := fun i => c i * (λ i - λ a)
        let λ' : α → ℝ := fun i => λ i - λ a
        have hc' : ∀ i ∈ s, c' i ≠ 0 := by
          intro i hi
          have hci : c i ≠ 0 := hc i (Finset.mem_insert_of_mem hi)
          have hia : i ≠ a := by
            intro hia
            subst i
            exact ha hi
          have hli : λ i ≠ λ a := by
            intro hEq
            have := hλ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s) hEq
            exact hia this
          exact mul_ne_zero hci (sub_ne_zero.mpr hli)
        have hλ' : Set.InjOn λ' (s : Set α) := by
          intro i hi j hj hij
          apply hλ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj)
          dsimp [λ'] at hij
          linarith
        obtain ⟨hdfin, hdcard⟩ := ih hs c' λ' hc' hλ'
        let g : ℝ → ℝ := normalizedExpSum a s c λ
        let g' : ℝ → ℝ := expSum s c' λ'
        have hgcont : Continuous g := by
          dsimp [g, normalizedExpSum]
          fun_prop
        have hgderiv : ∀ x, HasDerivAt g (g' x) x := by
          intro x
          simpa [g, g', c', λ'] using hasDerivAt_normalizedExpSum a s c λ x
        have hgfin : {x | g x = 0}.Finite :=
          zeroSet_finite_of_deriv_zeroSet_finite g g' hgcont hgderiv (by simpa [g'] using hdfin)
        have hgcard : Set.ncard {x | g x = 0} ≤ Set.ncard {x | g' x = 0} + 1 :=
          zeroSet_ncard_le_derivZeroSet_ncard_add_one g g' hgcont hgderiv
            (by simpa [g'] using hdfin)
        have hsets : {x | expSum (insert a s) c λ x = 0} = {x | g x = 0} := by
          ext x
          simp only [Set.mem_setOf_eq]
          simpa [g] using (normalizedExpSum_zero_iff a s ha c λ x).symm
        constructor
        · simpa [hsets] using hgfin
        · rw [hsets]
          calc
            Set.ncard {x | g x = 0} ≤ Set.ncard {x | g' x = 0} + 1 := hgcard
            _ ≤ (s.card - 1) + 1 := by
              gcongr
              simpa [g'] using hdcard
            _ = (insert a s).card - 1 := by
              simp [ha, hs.card_pos]
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        have hca : c a ≠ 0 := hc a (by simp)
        have hset : {x | expSum ({a} : Finset α) c λ x = 0} = ∅ := by
          ext x
          simp [expSum, hca]
        constructor
        · simp [hset]
        · simp [hset]

end
end TmlrAudit
