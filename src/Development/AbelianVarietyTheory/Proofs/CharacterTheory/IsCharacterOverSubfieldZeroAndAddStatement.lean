module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAdd
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_zero_and_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G], IsChar K L (0 : G → L) ∧ ∀ a b : G → L, IsChar K L a → IsChar K L b → IsChar K L (a + b) := by
  first | exact @GlobalTheory.BI.isChar_zero_and_add | exact GlobalTheory.BI.isChar_zero_and_add | (intros; apply GlobalTheory.BI.isChar_zero_and_add <;> assumption)
