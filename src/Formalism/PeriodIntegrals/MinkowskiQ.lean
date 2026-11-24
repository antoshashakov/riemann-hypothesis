module

public import Formalism.PeriodIntegrals.Minkowski
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI

def MinkowskiBoundQ : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℚ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
