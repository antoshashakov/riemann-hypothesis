module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.LatticeCountingTheorem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjPowOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointKernelBoundOfPointwiseBound
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBound
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepSetBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBound
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDimensionalRowsSpaceDiscreteSeriesCount
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalfStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagRareOfNonzeroFlagBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermAbsoluteVolumeBoundOfVolumeRatioInduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagProbabilityBoundOfVolumeRatioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKTypeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductio
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneTypeArith
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundOfDecGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableOfSupport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountFinal

theorem countingTheorem_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hV
  have hDec : GlobalTheory.DSId.DecGap := _root_.GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType
  have hPt : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hDec
  have hAbs : GlobalTheory.FlagMeas.AbsoluteVolume := _root_.GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep hV
  have hFM : GlobalTheory.FlagMeas.FlagMeasureBound := GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio hV
  have hFin := _root_.GlobalTheory.RowsFinMult.rows_finiteDimensional hDec hAbs
  have hNear := GlobalTheory.NearMod.nearModerate hFM GlobalTheory.T.flag_explicit_constant_le_exp_neg_half GlobalTheory.NearElement.near_unipotent hPt
  have hFar := _root_.GlobalTheory.Deep.farModerate_of_farBound hFM (GlobalTheory.FarTerms.farBound_of_ptBound hPt)
  have hRare := GlobalTheory.FlagRareProof.flagRare_of_nonzeroFlagBound (_root_.GlobalTheory.NonzeroFlag.nonzeroFlagBound hV)
  have hDeep := _root_.GlobalTheory.DeepRegion.deepBound hAbs (_root_.GlobalTheory.DeepKernel.deep_kernel_bound_of_ptBound hPt hFin)
  exact _root_.GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds hFin hFM hPt hNear hFar hRare hDeep

end GlobalTheory.CountFinal
