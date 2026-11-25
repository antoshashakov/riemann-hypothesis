module

public import Formalism.PeriodIntegrals.SplitIntLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitPrimeIntegers.ExistsUnitDiff
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem split_integral_local : PI.SplitIntLoc := PI.SplitIntLoc.Proof.main
