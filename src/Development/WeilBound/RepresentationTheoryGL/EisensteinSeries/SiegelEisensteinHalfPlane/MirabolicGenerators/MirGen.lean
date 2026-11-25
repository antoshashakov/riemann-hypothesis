module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfolding
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace PositivityTheory.RgEis.MG

theorem mirGen : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen :=
  fun hS hG hB hC hM hT hSph =>
    have hO := _root_.GlobalTheory.CompanionTheory.MirSides.sideOf hG hB
    have hZ := _root_.GlobalTheory.CompanionTheory.ZetaAlongK.zetaK hC
    _root_.GlobalTheory.CompanionTheory.EisMir.mirGen_of_core hS hSph _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem (_root_.GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem) hO (_root_.GlobalTheory.CompanionTheory.EisTestK.testK hG hB hT)
      (_root_.GlobalTheory.CompanionTheory.EisCore.wall_core hM _root_.GlobalTheory.CompanionTheory.RgEisDGood.dGood (_root_.GlobalTheory.CompanionTheory.RgEisMG.master _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem _root_.GlobalTheory.CompanionTheory.RgEisDGood.dGood _root_.GlobalTheory.CompanionTheory.RgEisHGood.hGood _root_.GlobalTheory.CompanionTheory.RgEisLeft.bGood) hO _root_.GlobalTheory.CompanionTheory.RgEisTerm.term hZ
        (_root_.GlobalTheory.CompanionTheory.RgEisSide.sideUnfold hC (_root_.GlobalTheory.CompanionTheory.RgEisUnfold.unfold hS _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem) _root_.GlobalTheory.CompanionTheory.RgEisLines.lines _root_.GlobalTheory.CompanionTheory.RgEisTerm.term hZ) (_root_.GlobalTheory.CompanionTheory.RgEisSide.sideConv hC hSph _root_.GlobalTheory.CompanionTheory.RgEisLines.lines _root_.GlobalTheory.CompanionTheory.RgEisTerm.term) (_root_.GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain hM))

end PositivityTheory.RgEis.MG
