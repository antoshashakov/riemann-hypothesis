module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.ExGenus

open Formalism.HermitianLatticesTheory

private theorem full_of_unimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hu : IsUnimodular h L) :
    Submodule.IsFullLattice K L := by
  exact { toIsLattice := hL, span_eq_top := Formalism.BasicNotions.HSpace.span_eq_top_of_unimodular hL.fg hu }


theorem mem_genus_of_isUnimodular : ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.TypeAsm.Std D large₂ → ∀ (X : HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 := by
  intro D large₂ hS _ _ Λ hΛ hU
  have hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := (GlobalTheory.TypeAsm.hostC D large₂ hS).1

  have hloc : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E L →
      (Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT L ↔
        ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt (VS D).hT P L) :=
    fun L hL => (Formalism.HermitianLatticesTheory.locDual (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT (VS D).herm
      Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range L hL.fg).2
  have hΛfull := full_of_unimodular (VS D).hT (VS D).herm hΛ hU
  have hL0full := full_of_unimodular (VS D).hT (VS D).herm
    (VS D).standardTuple_isLattice (VS D).baseLattice_isUnimodular
  refine ⟨hΛfull, fun P hP => ?_⟩

  exact GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt D.host.E (VS D).V (VS D).hT hCM (VS D).herm
    (VS D).nondeg (VS D).L0 Λ hL0full hΛfull P hP
    ((hloc _ (VS D).standardTuple_isLattice).1 (VS D).baseLattice_isUnimodular P hP) ((hloc Λ hΛ).1 hU P hP)

end GlobalTheory.RowsOrb.ExGenus
