module

public import Formalism.PeriodIntegrals.KerIso
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsDenomBackward
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem ordRelativeDet_finite : PI.KerIso.DetOrdFin := PI.KerDetFinW.detOrdFin
