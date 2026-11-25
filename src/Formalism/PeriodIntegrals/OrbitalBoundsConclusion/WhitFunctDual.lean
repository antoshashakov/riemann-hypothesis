module

public import Formalism.PeriodIntegrals.WhitFunctDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WhittakerFunctionalDual.StableOfIrreducible
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem whittaker_functional_dual : PI.WhitFunctDual := PI.WhitFunctDualWork.whitFunctDual_main
