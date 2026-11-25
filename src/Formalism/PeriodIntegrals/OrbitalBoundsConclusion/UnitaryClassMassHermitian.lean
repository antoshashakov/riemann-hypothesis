module

public import Formalism.PeriodIntegrals.UJClassMassAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UnitaryClassMass
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem unitary_class_mass_hermitian : PI.UJClassMass2.UJClassMass :=
  PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
