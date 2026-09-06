import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Vandermonde

namespace TmlrAudit

open scoped BigOperators

/-- The prescribed menu `β_j = 1 + j/M`. -/
def betaMenu {M : ℕ} (j : Fin M) : ℝ :=
  1 + (j : ℝ) / M

/-- The moment map from Appendix B. -/
def momentMap {M : ℕ} (v : Fin M → ℝ) (j : Fin M) : ℝ :=
  ∑ l : Fin M, Real.exp (betaMenu j * v l)

/-- The matrix written as `DF(a)` in the manuscript. -/
def momentJacobian {M : ℕ} (a : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun j l => betaMenu j * Real.exp (betaMenu j * a l)

/-- The Vandermonde nodes `q_l = exp(a_l/M)`. -/
def momentNode {M : ℕ} (a : Fin M → ℝ) (l : Fin M) : ℝ :=
  Real.exp (a l / M)

/-- A Vandermonde matrix over distinct real nodes has nonzero determinant. -/
lemma det_vandermonde_ne_zero_of_injective {M : ℕ} (q : Fin M → ℝ)
    (hq : Function.Injective q) :
    (Matrix.vandermonde q).det ≠ 0 := by
  rw [Matrix.det_vandermonde]
  simp only [Finset.prod_eq_zero_iff, not_exists, sub_eq_zero]
  intro i
  intro j hj hji
  exact (Finset.mem_Ioi.mp hj).ne' (hq hji)

/-- Injectivity of the base coordinates is preserved by the exponential node map. -/
lemma momentNode_injective {M : ℕ} (hM : 0 < M) (a : Fin M → ℝ)
    (ha : Function.Injective a) :
    Function.Injective (momentNode a) := by
  intro i j hij
  apply ha
  have hdiv : a i / (M : ℝ) = a j / (M : ℝ) := Real.exp_injective hij
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  apply (div_left_inj' hM0).mp
  simpa using hdiv

/-- The middle Vandermonde factor in the Jacobian is nonsingular. -/
lemma momentNode_vandermonde_det_ne_zero {M : ℕ} (hM : 0 < M) (a : Fin M → ℝ)
    (ha : Function.Injective a) :
    (Matrix.vandermonde (momentNode a)).det ≠ 0 :=
  det_vandermonde_ne_zero_of_injective _ (momentNode_injective hM a ha)

/-- Exact factorization `J = diag(β) * vandermonde(q)^T * diag(exp(a))`. -/
lemma momentJacobian_factorization {M : ℕ} (a : Fin M → ℝ) :
    momentJacobian a =
      Matrix.diagonal betaMenu * (Matrix.vandermonde (momentNode a))ᵀ *
        Matrix.diagonal (fun l => Real.exp (a l)) := by
  classical
  ext j l
  simp [momentJacobian, Matrix.mul_apply, momentNode]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  dsimp [betaMenu]
  ring

/-- Nonsingularity of the Jacobian at every injective base vector. -/
theorem momentJacobian_det_ne_zero {M : ℕ} (hM : 0 < M) (a : Fin M → ℝ)
    (ha : Function.Injective a) :
    (momentJacobian a).det ≠ 0 := by
  classical
  have hβ : ∀ j : Fin M, betaMenu j ≠ 0 := by
    intro j
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
    dsimp [betaMenu]
    positivity
  have hDβ : (Matrix.diagonal betaMenu : Matrix (Fin M) (Fin M) ℝ).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro j _hj
      exact hβ j)
  have hV : ((Matrix.vandermonde (momentNode a))ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact momentNode_vandermonde_det_ne_zero hM a ha
  have hDa : (Matrix.diagonal (fun l : Fin M => Real.exp (a l)) :
      Matrix (Fin M) (Fin M) ℝ).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro l _hl
      exact Real.exp_ne_zero _)
  rw [momentJacobian_factorization, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hDβ hV) hDa

end TmlrAudit
