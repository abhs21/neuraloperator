import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Vandermonde

namespace TmlrAudit

open scoped BigOperators
noncomputable section

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
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _hi
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  exact sub_ne_zero.mpr (hq.ne (Finset.mem_Ioi.mp hj).ne')

/-- Injectivity of the base coordinates is preserved by the exponential node map. -/
lemma momentNode_injective {M : ℕ} (hM : 0 < M) (a : Fin M → ℝ)
    (ha : Function.Injective a) :
    Function.Injective (momentNode a) := by
  intro i j hij
  apply ha
  have hdiv : a i / (M : ℝ) = a j / (M : ℝ) := Real.exp_injective hij
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  calc
    a i = (a i / (M : ℝ)) * (M : ℝ) := (div_mul_cancel₀ _ hM0).symm
    _ = (a j / (M : ℝ)) * (M : ℝ) := by rw [hdiv]
    _ = a j := div_mul_cancel₀ _ hM0

/-- The middle Vandermonde factor in the Jacobian is nonsingular. -/
lemma momentNode_vandermonde_det_ne_zero {M : ℕ} (hM : 0 < M) (a : Fin M → ℝ)
    (ha : Function.Injective a) :
    (Matrix.vandermonde (momentNode a)).det ≠ 0 :=
  det_vandermonde_ne_zero_of_injective _ (momentNode_injective hM a ha)

/-- Exact factorization `J = diag(β) * vandermonde(q)^T * diag(exp(a))`. -/
lemma momentJacobian_factorization {M : ℕ} (a : Fin M → ℝ) :
    momentJacobian a =
      Matrix.diagonal betaMenu * Matrix.transpose (Matrix.vandermonde (momentNode a)) *
        Matrix.diagonal (fun l => Real.exp (a l)) := by
  classical
  ext j l
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
    Matrix.vandermonde_apply]
  simp only [momentJacobian, momentNode]
  rw [← Real.exp_nat_mul]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  have hM : 0 < M := Nat.zero_lt_of_lt j.isLt
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  dsimp [betaMenu]
  field_simp [hM0]
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
  have hV : (Matrix.transpose (Matrix.vandermonde (momentNode a))).det ≠ 0 := by
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

end
end TmlrAudit
