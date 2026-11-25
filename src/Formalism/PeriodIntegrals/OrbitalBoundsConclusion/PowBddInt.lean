module

public import Formalism.PeriodIntegrals.PowBddInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.EvalIntMapEqZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Imports
import Supplements.MathlibImports.AnalysisAndTactics
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Development

@[expose] public section

theorem power_bounded_integral : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
