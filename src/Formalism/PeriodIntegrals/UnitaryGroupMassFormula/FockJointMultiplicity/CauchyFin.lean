module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauBFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHWOfShape
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.FJM

theorem cauchy_highest_weight : CauchyHW :=
  PI.FJMB.cauchyHW_of_shape PI.FJMX.minorProductDiagonal

end PI.FJM
