module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AnisotropicOfHenselAndSandwich
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.anisotropic_of_hensel_and_sandwich : StHensel → StSandwich → StAniso := by
  first | exact @GlobalTheory.CompanionTheory.HermAniso.aniso | exact GlobalTheory.CompanionTheory.HermAniso.aniso | (intros; apply GlobalTheory.CompanionTheory.HermAniso.aniso <;> assumption)
