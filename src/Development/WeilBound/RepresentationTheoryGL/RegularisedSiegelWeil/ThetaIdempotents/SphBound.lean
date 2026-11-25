module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeights
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisenstein
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleReality
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeights
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeights
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentity
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

namespace PositivityTheory.Rg.Rsw

theorem mapsExist : MapsExist := _root_.GlobalTheory.CompanionTheory.JacobiMaps.mapsExist
theorem htExist : HtExist := _root_.GlobalTheory.CompanionTheory.HtEx.htExist
theorem heckeEta : HeckeEta := _root_.GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta
theorem fjEis : FJEis := _root_.GlobalTheory.CompanionTheory.FJE.fjEis _root_.GlobalTheory.CompanionTheory.ZUnf.zUnfold _root_.GlobalTheory.CompanionTheory.ThTw.thTwist
theorem pcBound : PcBound := _root_.GlobalTheory.CompanionTheory.PcB.pcBound
theorem rSec : RSec := _root_.GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist htExist
theorem eisHol : EisHol := _root_.GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist htExist
theorem thTotal : ThTotal := _root_.GlobalTheory.CompanionTheory.ThTot.thTotal heckeEta
theorem cfFJ : CfFJ := _root_.GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound pcBound
theorem pcFc : PcFc := _root_.GlobalTheory.CompanionTheory.PcFc.target mapsExist GlobalTheory.T.fourier_zero_holds
theorem sphBound : SphBound := _root_.GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist htExist
theorem resMu : ResMu :=
  _root_.GlobalTheory.CompanionTheory.ResMu.resMu_main mapsExist htExist heckeEta fjEis pcBound rSec eisHol thTotal pcFc sphBound GlobalTheory.T.fourier_zero_holds GlobalTheory.T.coefficient_data_exists
theorem polar : Polar :=
  _root_.GlobalTheory.CompanionTheory.RswPolar.polar mapsExist htExist heckeEta _root_.GlobalTheory.CompanionTheory.Dblock.rightId _root_.GlobalTheory.CompanionTheory.PoleBound.poleReal fjEis pcBound rSec eisHol thTotal cfFJ pcFc sphBound

end PositivityTheory.Rg.Rsw
