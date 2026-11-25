module

public import Formalism.PeriodIntegrals.BallQuotLen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BallQuotientLength.LengthBallQuotientEqSumMulFdeg
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem ball_quotient_length : PI.BallQuotLen := PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main
