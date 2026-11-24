module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralLinearFormPiMatrixEqSumTrace
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix : ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ) (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k), (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  first | exact @GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace | exact GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace | (intros; apply GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace <;> assumption)
