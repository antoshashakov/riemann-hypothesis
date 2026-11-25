module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormula
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.unramified_local_formula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula | exact GlobalTheory.CompanionTheory.UnrDens.unrFormula | (intros; apply GlobalTheory.CompanionTheory.UnrDens.unrFormula <;> assumption)
