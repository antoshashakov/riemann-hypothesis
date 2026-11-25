module

public import Formalism.PeriodIntegrals.LongWeylElementSquare
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiDerivative.StarinvDeriv
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem phiDeriv_of (hW : PI.SwBig.LongWeylElementSquare) : PI.SwBig.PhiDeriv :=
  fun k r => PI.SwBig.PhiDerivW.main k r hW
