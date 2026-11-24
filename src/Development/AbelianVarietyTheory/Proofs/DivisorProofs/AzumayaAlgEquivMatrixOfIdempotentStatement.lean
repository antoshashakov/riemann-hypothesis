module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaAlgEquivMatrixOfIdempotent
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nonempty_algEquiv_matrix_of_isAzumaya_of_full_idempotent : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] (n : ℕ), Module.finrank A Λ = n ^ 2 → ∀ e : Λ, IsIdempotentElem e → (∀ y : Λ, ∃ c : A, e * y * e = c • e) → (∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.azumaya_algEquiv_matrix_of_idempotent) | (exact GlobalTheory.azumaya_algEquiv_matrix_of_idempotent) | (intros; apply GlobalTheory.azumaya_algEquiv_matrix_of_idempotent  <;> assumption)
