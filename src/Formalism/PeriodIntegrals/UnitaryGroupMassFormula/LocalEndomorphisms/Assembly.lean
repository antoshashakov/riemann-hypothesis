module

public import Formalism.PeriodIntegrals.LocalEnd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.ValSurjective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.AlgebraMapMemRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.IsUniformInducingOfVal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.LocalEndHomeoOf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.LocalEndW

theorem localEndHomeo_of_three (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt) :
    PI.LocalEndHomeo :=
  localEndHomeo_of hA hB1 hB2 valContinuous valSurjective

end PI.LocalEndW
