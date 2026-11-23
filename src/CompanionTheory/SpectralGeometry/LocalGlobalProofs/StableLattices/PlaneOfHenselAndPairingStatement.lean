module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneOfHenselAndPairing
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.plane_of_hensel_and_pairing : StHensel → StPairing → StPlane := by
  first | exact @GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing | exact GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing | (intros; apply GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing <;> assumption)
