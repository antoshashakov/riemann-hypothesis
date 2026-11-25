module

public import Formalism.RealPlaceAnalysis.Complexify
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

theorem jm_true (k : ℕ) : Formalism.REAL.Jm (fun _ : Fin k => true) = 1 := by
  simp [Formalism.REAL.Jm]

end PI.AprimeInfW
