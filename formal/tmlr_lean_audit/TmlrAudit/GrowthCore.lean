import TmlrAudit.LowerBoundCore

namespace TmlrAudit

open Finset

/-- The manuscript's explicit growth-function envelope `G_K(m)`. -/
def growthBound (K m : ℕ) : ℕ :=
  (m + 1) * (1 + (2 * K - 4) * m * (m - 1))

/-- Any finite family shattering `s` contains at least `2^|s|` distinct traces. -/
theorem pow_card_le_card_of_shatters {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (s : Finset α) (hs : 𝒜.Shatters s) :
    2 ^ #s ≤ #𝒜 := by
  rw [Finset.shatters_iff] at hs
  have hcard := congrArg Finset.card hs
  rw [Finset.card_powerset] at hcard
  rw [← hcard]
  exact Finset.card_image_le

/-- Once trace count is bounded by `G_K(m)`, shattering forces `2^m ≤ G_K(m)`. -/
theorem shattering_forces_power_le_growth {K m : ℕ}
    (𝒜 : Finset (Finset (Fin m)))
    (hcard : #𝒜 ≤ growthBound K m)
    (hs : 𝒜.Shatters (Finset.univ : Finset (Fin m))) :
    2 ^ m ≤ growthBound K m := by
  calc
    2 ^ m = 2 ^ #(Finset.univ : Finset (Fin m)) := by simp
    _ ≤ #𝒜 := pow_card_le_card_of_shatters 𝒜 Finset.univ hs
    _ ≤ growthBound K m := hcard

end TmlrAudit
