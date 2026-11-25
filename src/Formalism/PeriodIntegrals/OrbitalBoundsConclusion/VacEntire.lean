module

public import Formalism.PeriodIntegrals.VacEntire
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.VacuumEntire.AnalyticAtHfLeft
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem entireStatements_holds : PI.VacEntire.Target :=
  ⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩
