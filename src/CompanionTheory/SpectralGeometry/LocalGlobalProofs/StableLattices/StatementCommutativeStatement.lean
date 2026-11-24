module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementCommutative
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.StatementCommutative : StComm := by
  first | exact @GlobalTheory.CompanionTheory.Bernstein.stComm | exact GlobalTheory.CompanionTheory.Bernstein.stComm | (intros; apply GlobalTheory.CompanionTheory.Bernstein.stComm <;> assumption)
