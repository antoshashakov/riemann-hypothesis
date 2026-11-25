module

public import Formalism.PeriodIntegrals.ExistsGaugeMeasureForEachRank
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.ContinuousLmulM
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem exists_gaugeNormalizedStabilizer : PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank := fun r => ⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩
