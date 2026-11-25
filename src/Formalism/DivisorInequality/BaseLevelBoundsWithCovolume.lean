module

public import Formalism.DivisorInequality.StatementObj
public import Formalism.DivisorInequality.DivisorInequalityProofs.BaseLevelBoundsWithCovolumeHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.DivisorInequality

theorem boundsMu : BoundsMu := slope_bounds

end Formalism.DivisorInequality
