module

public import Formalism.PeriodIntegrals.WittUnram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.WittUnramMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem witt_unramified : PI.WittUnram :=
  PI.WittUnramWork.wittUnram_main
