module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteField
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField : ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ, ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  first | exact @GlobalTheory.CuspGL.TeichEmb.exists_teichmuller | exact GlobalTheory.CuspGL.TeichEmb.exists_teichmuller | (intros; apply GlobalTheory.CuspGL.TeichEmb.exists_teichmuller <;> assumption)
