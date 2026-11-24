module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup : ∀ (G : Type) [Group G] (T : Subgroup G), AbByP G → AbByP T := by
  first | exact @GlobalTheory.BI.AbByP.subgroup | exact GlobalTheory.BI.AbByP.subgroup | (intros; apply GlobalTheory.BI.AbByP.subgroup <;> assumption)
