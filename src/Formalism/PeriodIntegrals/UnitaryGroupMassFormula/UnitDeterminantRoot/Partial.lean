module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.DetMemOfEntries
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NormLeOneOfRoot
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NsmulRelIdxMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.UnitDetRootOf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

theorem unitDetRoot_of_global (h : GlobalLUnit) : PI.UnitDetRoot :=
  unitDetRoot_of detInK localStd h normOne rootStep conjMem conjLUnit

end PI.UnitaryGroupMassFormula.UnitDetRoot
