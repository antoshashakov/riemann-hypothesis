module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WittStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.WittStatement : StWitt := by
  first | exact @GlobalTheory.CompanionTheory.FlWitt.stWitt | exact GlobalTheory.CompanionTheory.FlWitt.stWitt | (intros; apply GlobalTheory.CompanionTheory.FlWitt.stWitt <;> assumption)
