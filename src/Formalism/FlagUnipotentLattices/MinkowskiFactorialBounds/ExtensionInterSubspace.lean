module

public import Mathlib.Analysis.Complex.Norm
import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
public import Formalism.LogSumExpBounds.StatementD
import Mathlib.Analysis.Matrix.Normed

@[expose] public section

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix

namespace Formalism.HermitianLatticeCounting.P

section Frob
open scoped Matrix.Norms.Frobenius

end Frob

noncomputable def n2 {N : ℕ} (v : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

section FrobG
open scoped Matrix.Norms.Frobenius

end FrobG


end Formalism.HermitianLatticeCounting.P
