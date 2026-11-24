module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.ProjectionStatement : StProj := by
  first | exact @GlobalTheory.CompanionTheory.FixedProj.stProj | exact GlobalTheory.CompanionTheory.FixedProj.stProj | (intros; apply GlobalTheory.CompanionTheory.FixedProj.stProj <;> assumption)
