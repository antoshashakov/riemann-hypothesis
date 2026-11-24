module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicRealisationHolomorphicMap
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.centralizer_separable_commutative : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (γ g h : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → g * γ = γ * g → h * γ = γ * h → g * h = h * g := by
  first | (exact @GlobalTheory.CentSep.centraliser_comm_of_separable) | (exact GlobalTheory.CentSep.centraliser_comm_of_separable) | (intros; apply GlobalTheory.CentSep.centraliser_comm_of_separable  <;> assumption)
