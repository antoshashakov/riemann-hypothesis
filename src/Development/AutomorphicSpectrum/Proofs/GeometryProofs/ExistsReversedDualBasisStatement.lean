module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReversedDualBasis
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)


theorem _root_.GlobalTheory.T.exists_reversed_dual_basis : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w : Module.Basis (Fin r) Ω (Fin r → Ω)),
    ∃ v : Module.Basis (Fin r) Ω (Fin r → Ω), ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis | exact GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis | (intros; apply GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis <;> assumption)
