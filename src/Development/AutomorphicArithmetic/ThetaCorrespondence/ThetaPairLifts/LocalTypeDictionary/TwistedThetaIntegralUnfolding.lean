module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellMassesAgainstLevelVolumesLargeDepth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProof
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExpansionZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowRealIteratedIntegralEqConstMulFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodReductionToFockVectorsLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodChangeOfMeasures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleCosetOffTwistPlacesLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedIterateEventuallyLarge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section
open GlobalTheory.RowClaim GlobalTheory.RowVal GlobalTheory.RowReal
namespace GlobalTheory.RowUnfLast
theorem twisted_theta_integral_unfolding : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := fun p c s =>
  have rel := _root_.GlobalTheory.RowRealInt.unfold_of_steps
  have hcv := _root_.GlobalTheory.RowVal.cellVan_holds
  have grp := _root_.GlobalTheory.RowGrpSplit.grpAt_big
  have it := _root_.GlobalTheory.T.twisted_iterate_chain
  have inv := _root_.GlobalTheory.RowInv.main
  have flat := GlobalTheory.RowFlatAsm.flatAt_big
  have supp := _root_.GlobalTheory.RowVal.big_suppOn_of_flat
  have rep := GlobalTheory.T.representation_at_every_place
  have val := _root_.GlobalTheory.RowVal.valAt_big
  have off := _root_.GlobalTheory.RowOneCos.offAt_big
  have tens := GlobalTheory.T.definitePeriod_depends_on_productFunction
  have vol := _root_.GlobalTheory.RowVal.volAt_big
  have wt := _root_.GlobalTheory.RowWt.wtAt_big
  have fock := _root_.GlobalTheory.FockRed.fockAt_big
  have bas := GlobalTheory.T.lastRow_unfolding_basicHypotheses
  have one := GlobalTheory.T.rowTest_support_families_staircase_cosets
  have rl := GlobalTheory.RowReal.realLine
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rel, grp⟩, it⟩, inv⟩, ⟨e, fl⟩⟩, supp⟩, rep⟩, val⟩, off⟩, tens⟩, vol⟩, wt⟩, fock⟩, bas⟩, one⟩, rl⟩, s⟩ =>
    rel grp it.1 it.2 inv ⟨e, supp e fl off inv tens bas, rep e, val e fl tens vol (wt e) fock bas one s⟩ rl s)
  (((((((((((((((((rel hcv).and grp).and (it p c)).and inv).and flat).and supp).and rep).and val).and off).and tens).and vol).and wt).and fock).and bas).and one).and rl).and s)
end GlobalTheory.RowUnfLast
end

section
open GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.twisted_theta_integral_unfolds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := by
  first | exact @_root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding | exact _root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding | (intros; apply _root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding <;> assumption)
end
