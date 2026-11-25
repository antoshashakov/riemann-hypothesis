module

public import Formalism.PeriodIntegrals.SigmaStarEx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.SigmaStarEx
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem sigma_star_exists : PI.SigmaStarEx := PI.SSE.sigmaStarEx
