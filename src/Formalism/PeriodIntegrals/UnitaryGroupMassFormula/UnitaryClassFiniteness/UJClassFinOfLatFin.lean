module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.ClassFiniteOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.RationalPointsDense
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.UJClassFinOf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.UnitaryGroupMassFormula.UJClassFin

theorem uJClassFin_of_latFin (hS : SigPos) (hA : AdelBounds) (hB : LatFin) : PI.UJClassFin.UJClassFin :=
  uJClassFin_of rational_points_dense (classFinite_of hS hA hB)

end PI.UnitaryGroupMassFormula.UJClassFin
