module

public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem quotient_invariant : PI.QuotInv := PI.QuotInvW.quotInv
