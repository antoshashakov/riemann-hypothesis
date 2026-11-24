module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgEquivMatrixGlueCrt
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct
open Function

theorem _root_.GlobalTheory.T.algEquiv_matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.matrix_glue_crt) | (exact GlobalTheory.matrix_glue_crt) | (intros; apply GlobalTheory.matrix_glue_crt  <;> assumption)
