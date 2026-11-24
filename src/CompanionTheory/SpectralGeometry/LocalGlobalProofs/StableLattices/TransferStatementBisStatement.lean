module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBis
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.TransferStatementBis : StTransfer := by
  first | exact @GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | exact GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | (intros; apply GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer <;> assumption)
