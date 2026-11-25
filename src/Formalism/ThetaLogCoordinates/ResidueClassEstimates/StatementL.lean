module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def ResidueClassLowerBound : Prop :=
  ∀ (r Q be c : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
        (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card : ℝ)

end Formalism.InvariantFactorPaths.BranchingDimensions
