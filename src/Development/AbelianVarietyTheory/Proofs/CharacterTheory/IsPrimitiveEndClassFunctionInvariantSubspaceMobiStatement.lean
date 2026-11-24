module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobi
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by
  first | exact @GlobalTheory.CuspGL.isPrimitive_psi | exact GlobalTheory.CuspGL.isPrimitive_psi | (intros; apply GlobalTheory.CuspGL.isPrimitive_psi <;> assumption)
