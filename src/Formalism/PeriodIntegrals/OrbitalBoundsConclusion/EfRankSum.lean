module

public import Formalism.PeriodIntegrals.EfRankSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.EfRankSumMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem ramificationDegreeSum : PI.EfRankSum := PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
