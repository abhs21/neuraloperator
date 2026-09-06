import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Fintype.Powerset

namespace TmlrAudit

open Finset

/-- The trace produced on the `m` designated points by candidate `j`. -/
def traceSet {m M : ℕ} (hit : Fin M → Fin m → Bool) (j : Fin M) : Finset (Fin m) :=
  Finset.univ.filter fun i => hit j i = true

/-- The finite set family of all traces produced by the candidate menu. -/
def traceFamily {m M : ℕ} (hit : Fin M → Fin m → Bool) : Finset (Finset (Fin m)) :=
  Finset.univ.image (traceSet hit)

lemma traceSet_mem_traceFamily {m M : ℕ} (hit : Fin M → Fin m → Bool) (j : Fin M) :
    traceSet hit j ∈ traceFamily hit := by
  classical
  simp [traceFamily]

/-- If every subset is realized by one candidate, the trace family shatters all `m` points. -/
theorem traceFamily_shatters_of_realizes {m M : ℕ}
    (hit : Fin M → Fin m → Bool)
    (code : Finset (Fin m) → Fin M)
    (hrealize : ∀ A i, hit (code A) i = true ↔ i ∈ A) :
    (traceFamily hit).Shatters (Finset.univ : Finset (Fin m)) := by
  classical
  intro A _hA
  refine ⟨traceSet hit (code A), traceSet_mem_traceFamily hit (code A), ?_⟩
  ext i
  simp [traceSet, hrealize A i]

/-- Realizing all subsets forces VC dimension at least `m`. -/
theorem vcDim_traceFamily_ge {m M : ℕ}
    (hit : Fin M → Fin m → Bool)
    (code : Finset (Fin m) → Fin M)
    (hrealize : ∀ A i, hit (code A) i = true ↔ i ∈ A) :
    m ≤ (traceFamily hit).vcDim := by
  have hs := traceFamily_shatters_of_realizes hit code hrealize
  simpa using hs.card_le_vcDim

/-- `M ≥ 2^m` is the finite-cardinality condition needed to inject all subsets. -/
theorem exists_subset_embedding {m M : ℕ} (hpow : 2 ^ m ≤ M) :
    Nonempty (Finset (Fin m) ↪ Fin M) := by
  rw [Function.Embedding.nonempty_iff_card_le]
  simpa using hpow

/-- A canonical noncomputable subset-to-candidate code under `2^m ≤ M`. -/
noncomputable def subsetCode {m M : ℕ} (hpow : 2 ^ m ≤ M) :
    Finset (Fin m) ↪ Fin M :=
  Classical.choice (exists_subset_embedding hpow)

/-- Paper-facing combinatorial lower-bound interface. -/
theorem vcDim_ge_of_power_budget {m M : ℕ} (hpow : 2 ^ m ≤ M)
    (hit : Fin M → Fin m → Bool)
    (hrealize : ∀ A i, hit (subsetCode hpow A) i = true ↔ i ∈ A) :
    m ≤ (traceFamily hit).vcDim := by
  exact vcDim_traceFamily_ge hit (subsetCode hpow) hrealize

end TmlrAudit
