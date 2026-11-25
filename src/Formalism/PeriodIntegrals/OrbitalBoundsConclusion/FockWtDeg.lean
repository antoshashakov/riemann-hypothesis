module

public import Formalism.PeriodIntegrals.FockDegreeTwoParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockWeightDegree.ExistsMonomialWeight
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem highestWeightDegree_le : PI.FockDegreeTwoParts.WtDeg := PI.FockWtDegWork.wtDeg
