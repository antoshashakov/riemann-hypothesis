module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.MovingStatement : StMove := by
  first | exact @GlobalTheory.CompanionTheory.CartanMove.stMove | exact GlobalTheory.CompanionTheory.CartanMove.stMove | (intros; apply GlobalTheory.CompanionTheory.CartanMove.stMove <;> assumption)
