module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectors
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.GL_transitive_nonzero_vectors : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | exact GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | (intros; apply GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows <;> assumption)
