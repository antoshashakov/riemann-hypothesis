module

public import Formalism.PeriodIntegrals.ClassNumImQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ClassNumberIntegrality.HalfIntegral
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem imag_quadratic_integral_basis : PI.ClassNumImQ.IntBasis :=
  PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
