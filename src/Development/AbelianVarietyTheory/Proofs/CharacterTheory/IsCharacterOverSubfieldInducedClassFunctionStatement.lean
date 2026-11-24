module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (ind H ψ) := by
  first | exact @GlobalTheory.BI.isChar_ind | exact GlobalTheory.BI.isChar_ind | (intros; apply GlobalTheory.BI.isChar_ind <;> assumption)
