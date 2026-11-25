module

public import Formalism.PeriodIntegrals.Minkowski
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.CharpolyDvdOfPowEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.MinkowskiBoundOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSum
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem card_dvd_minkowskiNumber : PI.MinkowskiBound :=
  PI.Mk.minkowskiBound_of_steps PI.Mk.traceStep PI.Mk.powerSumStep
