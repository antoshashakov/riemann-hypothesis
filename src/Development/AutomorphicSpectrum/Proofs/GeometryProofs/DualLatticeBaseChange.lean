module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualBaseChange
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dual_baseChange_fractionField : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) :=
  @PositivityTheory.Xgn.exists_dual_base_change

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
