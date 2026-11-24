module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockEmbeddingGLInverse
import Supplements.MathlibImports.AnalysisAndTactics
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.block_embedding_GL_inverse : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d → ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | (intros; apply GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb <;> assumption)
