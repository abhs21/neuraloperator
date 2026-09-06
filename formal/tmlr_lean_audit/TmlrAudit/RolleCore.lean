import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card

namespace TmlrAudit

/-- A finite collection of zeros of a differentiable function has at most one more
point than any finite set containing every derivative zero. -/
theorem rootFinset_card_le_derivZeroFinset_add_one
    (f f' : ℝ → ℝ) (hf : Continuous f)
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (s t : Finset ℝ)
    (hs : ∀ x ∈ s, f x = 0)
    (ht : ∀ x, f' x = 0 → x ∈ t) :
    s.card ≤ t.card + 1 := by
  refine (Finset.card_le_sdiff_of_interleaved ?_).trans ?_
  · intro x hx y hy hxy _hgap
    obtain ⟨z, hzI, hdz⟩ :=
      exists_deriv_eq_zero hxy hf.continuousOn ((hs x hx).trans (hs y hy).symm)
    have hz' : f' z = 0 := by
      rw [← (hfd z).deriv]
      exact hdz
    exact ⟨z, ht z hz', hzI.1, hzI.2⟩
  · exact Nat.add_le_add_right (Finset.card_le_card Finset.sdiff_subset) 1

/-- If the derivative has finitely many zeros, then the function has finitely many zeros. -/
theorem zeroSet_finite_of_deriv_zeroSet_finite
    (f f' : ℝ → ℝ) (hf : Continuous f)
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hderiv : {x | f' x = 0}.Finite) :
    {x | f x = 0}.Finite := by
  let t : Finset ℝ := hderiv.toFinset
  by_contra hzero
  have hInf : Set.Infinite {x | f x = 0} := hzero
  obtain ⟨s, hsSub, hsCard⟩ := hInf.exists_subset_card_eq (t.card + 2)
  have hbound : s.card ≤ t.card + 1 :=
    rootFinset_card_le_derivZeroFinset_add_one f f' hf hfd s t
      (by
        intro x hx
        exact hsSub (by simpa using hx))
      (by
        intro x hx
        simpa [t] using hx)
  omega

/-- Rolle's theorem as a cardinality inequality for zero sets. -/
theorem zeroSet_ncard_le_derivZeroSet_ncard_add_one
    (f f' : ℝ → ℝ) (hf : Continuous f)
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hderiv : {x | f' x = 0}.Finite) :
    Set.ncard {x | f x = 0} ≤ Set.ncard {x | f' x = 0} + 1 := by
  have hzero := zeroSet_finite_of_deriv_zeroSet_finite f f' hf hfd hderiv
  have hbound := rootFinset_card_le_derivZeroFinset_add_one f f' hf hfd
    hzero.toFinset hderiv.toFinset
    (by
      intro x hx
      simpa using hx)
    (by
      intro x hx
      simpa using hx)
  simpa [Set.ncard_eq_toFinset_card _ hzero,
    Set.ncard_eq_toFinset_card _ hderiv] using hbound

end TmlrAudit
