module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InvarianceOfDomain.Statement : Prop :=
  ∀ (n : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → Fin n → ℝ),
    IsOpen U → ContinuousOn f U → Set.InjOn f U → IsOpen (f '' U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
