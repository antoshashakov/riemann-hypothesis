module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReversedDualTriangular
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)


theorem _root_.GlobalTheory.T.reversed_dual_triangular : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri | exact GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri | (intros; apply GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri <;> assumption)
