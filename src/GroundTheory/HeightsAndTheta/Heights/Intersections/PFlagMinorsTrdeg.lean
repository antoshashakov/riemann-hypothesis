module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToDual
import Supplements.MathlibImports.AnalysisAndTactics
public import Mathlib.Algebra.Field.Defs

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section

variable (F : Type) [Field F] (n : ℕ)

abbrev PivotIdx := Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
