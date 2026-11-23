module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistenceOfSandwichStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.existence_of_sandwich_statement : StSandwich → StExists := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | exact GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | (intros; apply GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich <;> assumption)
