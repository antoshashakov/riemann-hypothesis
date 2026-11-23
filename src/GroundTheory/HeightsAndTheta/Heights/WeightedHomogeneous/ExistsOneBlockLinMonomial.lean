module

import Supplements.MathlibImports.AnalysisAndTactics
public import Lean.Meta.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (IsMultiHomog IsArithVar mCoordIdeal secM MRing MRingOver)

noncomputable section

section Values

variable {K : Type} [Field K] {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ)

end Values

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
