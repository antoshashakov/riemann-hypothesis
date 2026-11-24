module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplex
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex : ∀ (G : Type) [Group G] (χ : G → ℂ), (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔ IsChar ℂ ℂ χ := by
  first | exact @GlobalTheory.BI.matrixChar_iff_isChar | exact GlobalTheory.BI.matrixChar_iff_isChar | (intros; apply GlobalTheory.BI.matrixChar_iff_isChar <;> assumption)
