module

import Supplements.MathlibImports.AnalysisAndTactics
public import Lean.Meta.Basic
public import Mathlib.Data.Fintype.Defs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Module Matrix
open scoped ComplexOrder

noncomputable section

section Embedding

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}


end Embedding

end

end GroundTheory.Heights₂.Heights
