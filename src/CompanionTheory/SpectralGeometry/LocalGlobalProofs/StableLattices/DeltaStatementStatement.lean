module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DeltaStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.DeltaStatement : StDelta := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stDelta | exact GlobalTheory.CompanionTheory.RgFl.stDelta | (intros; apply GlobalTheory.CompanionTheory.RgFl.stDelta <;> assumption)
