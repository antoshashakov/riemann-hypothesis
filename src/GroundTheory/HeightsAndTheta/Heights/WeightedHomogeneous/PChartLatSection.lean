module

import Supplements.MathlibImports.AnalysisAndTactics
public import Lean.Meta.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ChartLatSection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]



end ChartLatSection


end

end GroundTheory.Heights₂.Heights
