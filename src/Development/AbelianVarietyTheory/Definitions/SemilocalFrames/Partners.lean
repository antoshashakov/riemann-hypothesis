module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc Matrix

namespace GlobalTheory.SgDen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


def densF (q : ℕ) (η : ℝ) (n a c : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc (n + 1 - a - c) n, (1 - (η * (q : ℝ)⁻¹) ^ i)

variable [MeasurableSpace E]


end GlobalTheory.SgDen
