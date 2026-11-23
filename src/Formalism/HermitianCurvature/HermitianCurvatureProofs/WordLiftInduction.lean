module

import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.HermitianCurvature.LevelRecursionCondNeeded
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace Formalism.FourierDecayAlt.P.WordLiftInduction

open Finset Polynomial Formalism.FourierDecayAlt.F7

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

end

end Formalism.FourierDecayAlt.P.WordLiftInduction

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7

end Formalism.FourierDecayAlt.P
