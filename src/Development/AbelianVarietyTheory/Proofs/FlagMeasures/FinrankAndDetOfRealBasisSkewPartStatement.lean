module

public import Formalism.RealPlaceAnalysis.Complexify
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankAndDetOfRealBasisSkewPart
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.finrank_and_det_of_real_basis_skew_part : ∀ (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) → LinearIndependent ℝ E → (∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ), (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) → LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  first | exact @GlobalTheory.RealFormBasis.finrank_and_det | exact GlobalTheory.RealFormBasis.finrank_and_det | (intros; apply GlobalTheory.RealFormBasis.finrank_and_det <;> assumption)
