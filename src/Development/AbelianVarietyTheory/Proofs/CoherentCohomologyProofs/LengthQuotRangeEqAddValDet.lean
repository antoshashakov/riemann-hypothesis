module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

@[expose] public section

namespace GlobalTheory

open IsDiscreteValuationRing

section CokernelLength

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_quot_range_eq_addVal_det {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) :=
  GlobalTheory.length_quotient_range_eq_addVal_det f

end CokernelLength

end GlobalTheory
