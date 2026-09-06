import TmlrAudit.RolleCore
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace TmlrAudit

open scoped BigOperators
noncomputable section

/-- A finite real exponential sum indexed by a finset. -/
def expSum {α : Type*} [DecidableEq α] (I : Finset α)
    (c lam : α → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ I, c i * Real.exp (lam i * x)

/-- Derivative of a finite exponential sum. -/
lemma hasDerivAt_expSum {α : Type*} [DecidableEq α]
    (I : Finset α) (c lam : α → ℝ) (x : ℝ) :
    HasDerivAt (expSum I c lam)
      (∑ i ∈ I, c i * lam i * Real.exp (lam i * x)) x := by
  unfold expSum
  apply HasDerivAt.fun_sum
  intro i _hi
  convert HasDerivAt.const_mul (c i)
    ((Real.hasDerivAt_exp (lam i * x)).comp x (hasDerivAt_const_mul (lam i))) using 1 <;>
    try ring

lemma continuous_expSum {α : Type*} [DecidableEq α]
    (I : Finset α) (c lam : α → ℝ) :
    Continuous (expSum I c lam) := by
  unfold expSum
  fun_prop

/-- Normalize an exponential sum by one distinguished exponent. -/
def normalizedExpSum {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (c lam : α → ℝ) (x : ℝ) : ℝ :=
  c a + ∑ i ∈ s, c i * Real.exp ((lam i - lam a) * x)

lemma normalizedExpSum_eq_factor {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (ha : a ∉ s) (c lam : α → ℝ) (x : ℝ) :
    normalizedExpSum a s c lam x =
      Real.exp (-lam a * x) * expSum (insert a s) c lam x := by
  classical
  simp only [normalizedExpSum, expSum, Finset.sum_insert, ha, not_false_eq_true]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · have hexp : Real.exp (-lam a * x) * Real.exp (lam a * x) = 1 := by
      rw [← Real.exp_add]
      have harg : -lam a * x + lam a * x = 0 := by ring
      rw [harg, Real.exp_zero]
    calc
      c a = c a * 1 := by simp
      _ = c a * (Real.exp (-lam a * x) * Real.exp (lam a * x)) := by rw [hexp]
      _ = Real.exp (-lam a * x) * (c a * Real.exp (lam a * x)) := by ring
  · apply Finset.sum_congr rfl
    intro i hi
    have hexp : Real.exp (-lam a * x) * Real.exp (lam i * x) =
        Real.exp ((lam i - lam a) * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      c i * Real.exp ((lam i - lam a) * x) =
          c i * (Real.exp (-lam a * x) * Real.exp (lam i * x)) := by rw [hexp]
      _ = Real.exp (-lam a * x) * (c i * Real.exp (lam i * x)) := by ring

lemma normalizedExpSum_zero_iff {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (ha : a ∉ s) (c lam : α → ℝ) (x : ℝ) :
    normalizedExpSum a s c lam x = 0 ↔ expSum (insert a s) c lam x = 0 := by
  rw [normalizedExpSum_eq_factor a s ha c lam x, mul_eq_zero]
  simp

/-- The derivative of the normalized sum has one fewer exponential term. -/
lemma hasDerivAt_normalizedExpSum {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (c lam : α → ℝ) (x : ℝ) :
    HasDerivAt (normalizedExpSum a s c lam)
      (expSum s (fun i => c i * (lam i - lam a)) (fun i => lam i - lam a) x) x := by
  unfold normalizedExpSum expSum
  have hsum : HasDerivAt (fun y => ∑ i ∈ s, c i * Real.exp ((lam i - lam a) * y))
      (∑ i ∈ s, c i * (lam i - lam a) * Real.exp ((lam i - lam a) * x)) x := by
    apply HasDerivAt.fun_sum
    intro i _hi
    convert HasDerivAt.const_mul (c i)
      ((Real.hasDerivAt_exp ((lam i - lam a) * x)).comp x
        (hasDerivAt_const_mul (lam i - lam a))) using 1 <;>
      try ring
  convert (hasDerivAt_const x (c a)).add hsum using 1 <;>
    try ring

/-- A nonzero finite sum of exponentials with distinct exponents has at most one fewer
real zero than the number of terms. This is the manuscript's Lemma A.1 in finite-set form. -/
theorem expSum_zero_set_finite_and_ncard_le {α : Type*} [DecidableEq α]
    (I : Finset α) (hI : I.Nonempty) (c lam : α → ℝ)
    (hc : ∀ i ∈ I, c i ≠ 0)
    (hlam : Set.InjOn lam (I : Set α)) :
    {x | expSum I c lam x = 0}.Finite ∧
      Set.ncard {x | expSum I c lam x = 0} ≤ I.card - 1 := by
  induction I using Finset.induction_on generalizing c lam with
  | empty => simp at hI
  | @insert a s ha ih =>
      by_cases hs : s.Nonempty
      · let c' : α → ℝ := fun i => c i * (lam i - lam a)
        let lam' : α → ℝ := fun i => lam i - lam a
        have hc' : ∀ i ∈ s, c' i ≠ 0 := by
          intro i hi
          have hci : c i ≠ 0 := hc i (Finset.mem_insert_of_mem hi)
          have hia : i ≠ a := by
            intro hia
            subst i
            exact ha hi
          have hli : lam i ≠ lam a := by
            intro hEq
            have hEqIdx := hlam (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s) hEq
            exact hia hEqIdx
          exact mul_ne_zero hci (sub_ne_zero.mpr hli)
        have hlam' : Set.InjOn lam' (s : Set α) := by
          intro i hi j hj hij
          apply hlam (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj)
          dsimp [lam'] at hij
          linarith
        obtain ⟨hdfin, hdcard⟩ := ih hs c' lam' hc' hlam'
        let g : ℝ → ℝ := normalizedExpSum a s c lam
        let g' : ℝ → ℝ := expSum s c' lam'
        have hgcont : Continuous g := by
          change Continuous (fun x : ℝ => c a + ∑ i ∈ s, c i * Real.exp ((lam i - lam a) * x))
          fun_prop
        have hgderiv : ∀ x, HasDerivAt g (g' x) x := by
          intro x
          simpa [g, g', c', lam'] using hasDerivAt_normalizedExpSum a s c lam x
        have hgfin : {x | g x = 0}.Finite :=
          zeroSet_finite_of_deriv_zeroSet_finite g g' hgcont hgderiv (by simpa [g'] using hdfin)
        have hgcard : Set.ncard {x | g x = 0} ≤ Set.ncard {x | g' x = 0} + 1 :=
          zeroSet_ncard_le_derivZeroSet_ncard_add_one g g' hgcont hgderiv
            (by simpa [g'] using hdfin)
        have hsets : {x | expSum (insert a s) c lam x = 0} = {x | g x = 0} := by
          ext x
          simp only [Set.mem_setOf_eq]
          simpa [g] using (normalizedExpSum_zero_iff a s ha c lam x).symm
        constructor
        · rw [hsets]
          exact hgfin
        · rw [hsets]
          calc
            Set.ncard {x | g x = 0} ≤ Set.ncard {x | g' x = 0} + 1 := hgcard
            _ ≤ (s.card - 1) + 1 := by
              gcongr
              simpa [g'] using hdcard
            _ = (insert a s).card - 1 := by
              have hspos : 0 < s.card := hs.card_pos
              simp [ha]
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        have hca : c a ≠ 0 := hc a (by simp)
        have hset : {x | expSum (insert a (∅ : Finset α)) c lam x = 0} = ∅ := by
          ext x
          simp [expSum, hca]
        rw [hset]
        simp

end
end TmlrAudit
