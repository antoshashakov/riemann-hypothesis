module

public import Formalism.PeriodIntegrals.KerIso
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelOrder.ValNatCastEqOne
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem ordRelativeDet_independence : PI.KerIso.DetOrdIndep :=
  PI.KerIso.DetOrdW.detOrdIndep
