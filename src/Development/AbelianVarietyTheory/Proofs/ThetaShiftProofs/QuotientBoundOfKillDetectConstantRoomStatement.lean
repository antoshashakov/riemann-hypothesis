module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegree
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFamilyFunctionalBoundedLinearOnCuspFor
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBoundStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmValueLineLengthConjEqStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LamDegreeParameters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ModelsAtOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NdegLineOptionLe
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QbridgeOfNumGood
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QuotientBoundOfKillDetectConstantRoom
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumPf
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalToGlobal.ProjectiveLattices.RecConj
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

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem _root_.GlobalTheory.T.quotientBound_of_kill_detect_constantRoom : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D) (Ck Ch Ah C₀ A₀ Cd Ad : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h) j ka → KillQ h j ka CR Tt cc → DetectQ h j ka CR Tt cc → 1 ≤ zBase large₂ → 0 ≤ C₀ → 0 ≤ Cd → RoomAt large₂ j ka CR Tt cc C₀ A₀ →
    Real.log (@Module.finrank T.Q.c.F ((recB h).Cusp j ka) _
      ((recB h).acgC j ka).toAddCommMonoid ((recB h).modC j ka) : ℝ) ≤
      WeightFamilies.PPv D large₂ Cd Ad * ka.size →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.QAt large₂ (recB h) j ka CR Ck Ch Ah (Ch + 3 * C₀ + Cd) (max Ah (max A₀ Ad)) Tt cc := by
      exact GlobalTheory.ArcCM.qat_of_kill_detect
