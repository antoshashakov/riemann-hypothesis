module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSBase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSLocA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LsLat
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem lattice_modification : LatStep := latStep_of_parts lsLat lsOne lsLoc

end PI.UnitaryGroupMassFormula.UJClassMass
