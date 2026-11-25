module

public import Formalism.PeriodIntegrals.ExpTri
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.PsumEqRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SpecExists
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.ET

theorem expTri_of_horn (hH : Horn) : PI.ExpTri :=
  expTri_of specExists hsEq hH abelSq euclTri

end PI.ET
