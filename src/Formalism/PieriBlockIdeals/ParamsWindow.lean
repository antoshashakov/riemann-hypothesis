module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

def lamOf (N : ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := U i - ((N : ℤ) - 1 - (i : ℤ))

end Formalism.CohomologicalDescent
