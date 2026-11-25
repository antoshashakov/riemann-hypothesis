module

public import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundFull
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.GlobalBoundRefinements
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField

namespace Formalism.DivisionValues

theorem divIneqRecord : DivIneqRecord := divisor_inequality_explicit

end Formalism.DivisionValues
