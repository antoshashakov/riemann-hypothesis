module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeAlgebraStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.HeckeAlgebraTheorem : StHecke := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBern.stHecke | exact GlobalTheory.CompanionTheory.HeckeBern.stHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBern.stHecke <;> assumption)
