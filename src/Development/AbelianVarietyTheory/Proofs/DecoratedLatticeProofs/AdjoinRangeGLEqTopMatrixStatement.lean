module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdjoinRangeGLEqTopMatrix
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.SatakeDualWeyl.Statement

@[expose] public section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.adjoin_range_GL_eq_top_matrix : ∀ (R : Type) [CommRing R] (n : ℕ), Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  first | exact @GlobalTheory.adjoin_range_GL_eq_top | exact GlobalTheory.adjoin_range_GL_eq_top | (intros; apply GlobalTheory.adjoin_range_GL_eq_top <;> assumption)
