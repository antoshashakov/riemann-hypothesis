module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryExistsSkewLog
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_skewHermitian_log_of_unitary : ∀ (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ), kᴴ * k = 1 → ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  first | exact @GlobalTheory.unitary_exists_skew_log | exact GlobalTheory.unitary_exists_skew_log | (intros; apply GlobalTheory.unitary_exists_skew_log <;> assumption)
