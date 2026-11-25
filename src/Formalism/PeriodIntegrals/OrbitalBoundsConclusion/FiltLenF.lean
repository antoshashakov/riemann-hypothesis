module

public import Formalism.PeriodIntegrals.FiltLenF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiltrationLength.FiltLenFMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem filtration_length_bound : PI.FiltLenF := PI.FiltrationLength.filtLenF_main
