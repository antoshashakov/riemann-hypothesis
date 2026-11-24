module

public import Formalism.RealPlaceAnalysis.StatementB
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrix
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix : ∀ {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → ∀ k : ℕ, Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  first | exact @GlobalTheory.etr_conj_scalar_matrix | exact GlobalTheory.etr_conj_scalar_matrix | (intros; apply GlobalTheory.etr_conj_scalar_matrix <;> assumption)
