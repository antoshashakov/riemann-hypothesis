module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasisReTraceMulConjTranspose
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_orthonormal_basis_re_trace_mul_conjTranspose' : ∀ (n : ℕ) (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧ U = Submodule.span ℝ (Set.range E) := by
  first | exact @GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose | exact GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose | (intros; apply GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose <;> assumption)
