module

public import Formalism.PeriodIntegrals.LocHerm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.IsFieldOfNonsq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.ProjOfFreeIdem
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem projectiveOverOrder : PI.LocHerm.LocOProj :=
  PI.LocHerm.OProj.locOProj_of PI.LocHerm.OProj.sqCase PI.LocHerm.OProj.nonSqCase
