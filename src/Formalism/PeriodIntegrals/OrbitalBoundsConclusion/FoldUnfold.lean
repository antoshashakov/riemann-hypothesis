module

public import Formalism.PeriodIntegrals.FoldUnfold
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingIdentity.FoldUnfoldMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem lintegralTransversalSum : PI.FoldUnfold.FoldUnfold :=
  PI.FoldUnfold.UnitaryGroupMassFormula.foldUnfold_main
