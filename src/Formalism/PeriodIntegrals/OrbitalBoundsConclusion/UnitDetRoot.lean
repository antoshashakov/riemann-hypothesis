module

public import Formalism.PeriodIntegrals.UnitDetRoot
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.Partial
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem unit_det_root_of_unity : PI.UnitDetRoot :=
  PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of_global PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit
