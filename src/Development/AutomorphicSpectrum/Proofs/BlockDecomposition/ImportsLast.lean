module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOrbitalIntegralUnipotent
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerate
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainProperty
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFrameIdentities
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrability
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelFibers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactors
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScaling
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentShiftInvariance
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ D W b₀ hb x₀ hx
  have hDom := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.dom
  have hOF := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound hLat
  have hZ := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq
  have hA := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq
  have hJ := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds
  have hB := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.jnBl
  have hE := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action
  have hS := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.shift
  have hL := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.ikLint
  have hF := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds
  refine ⟨nuT hn I μ x₀, ⟨_root_.GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT D n t B W d hn I μ hμ b₀ hb x₀ hx, _root_.GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => _root_.GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac hQK _root_.GlobalTheory.CompanionTheory.ColumnSplitting.LawPf.law D n t B W d hn I μ hμ x₀ h,
    fun y _ => _root_.GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => _root_.GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov D n t B W d hn I μ hμ x₀ g⟩,
    _root_.GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, _root_.GlobalTheory.CompanionTheory.ColumnSplitting.continuous_orb_shear hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
