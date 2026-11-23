module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def hk (s : ℝ) (w : ℂ) : ℂ := (w ^ 2)⁻¹ * ((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)

end Formalism.L2.Th1.F
