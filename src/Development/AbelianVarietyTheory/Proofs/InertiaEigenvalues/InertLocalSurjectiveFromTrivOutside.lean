module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertSurj

theorem exists_supported (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (m : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ z : AL L, compAt L v z = m ∧ ∀ u, u ≠ v → compAt L u z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, h⟩ := GlobalTheory.InertUmax.tensor_decomp b m
  refine ⟨b 0 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v a +
    b 1 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same, h]
  · intro u hu
    rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.InertUmax.compAt_tmul]
    simp [conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, GlobalTheory.InertUmax.compAt_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.InertSurj
