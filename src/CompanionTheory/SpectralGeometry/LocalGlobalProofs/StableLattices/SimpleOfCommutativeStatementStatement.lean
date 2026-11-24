module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleOfCommutativeStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.simple_of_commutative_statement : StComm → StSimple := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | exact GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm <;> assumption)
