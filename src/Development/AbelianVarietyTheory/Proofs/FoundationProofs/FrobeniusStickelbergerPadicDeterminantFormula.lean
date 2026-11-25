module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLog
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDeterminantDefectOnLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerTaylorDefectEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransport
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLines
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

theorem frobenius_stickelberger_padic_determinant_formula : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := _root_.GlobalTheory.FrobStick.AtData.atData D p cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  obtain ⟨hAa, hBa, hS, hAv, hBv⟩ := _root_.GlobalTheory.FrobStick.colAB_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hCa, hCv⟩ := _root_.GlobalTheory.FrobStick.colC_atU _root_.GlobalTheory.DerivTransport.atU_deriv p g hq hL h2 h3 hσ v hv hw
  have hF : ∀ j, AlgEnt (![colA g.abelian₂, colB g.abelian₂ v, colC g.abelian₂ v] j) := by
    intro j; fin_cases j
    exacts [hAa, hBa, hCa]
  have h6 := _root_.GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero p g.lam _ (sgStar g.abelian₂) hF hσ (_root_.GlobalTheory.FrobStick.tay_defect_eq_zero _root_.GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines _root_.GlobalTheory.FrobStick.defect_line _root_.GlobalTheory.FrobStick.sgStar_cube_det_cplx g.abelian₂ hL v hv)
  obtain ⟨c0, c1, c2, c3, h7⟩ := _root_.GlobalTheory.FrobStick.SubstLog.subst_log_formula p g ok
  have h8 := h7 ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) _ _ h6
  have e : ∀ F : ℂ → ℂ, (PowerSeries.subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) (GL3Theta.ser1 g.lam F) : PowerSeries ℂ_[p]) = g.atU F :=
    fun F => (GlobalTheory.SerTransport.atU_eq g F).symm
  simp only [e, hS] at h8
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have h := congrArg PowerSeries.constantCoeff hq
    simpa using h
  refine _root_.GlobalTheory.FrobStick.det_column_ops p (ePhi1 g.lam g.abelian₂ g.C g.wq) g.wq ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) g.C.r g.W.a₁ g.W.a₃ _ _ _ _ (Units.ne_zero _) hw0 c0 c1 c2 c3 ?_
  rw [← h8]
  congr 1
  ext i j
  fin_cases j <;> simp [hAv, hBv, hCv]

end GlobalTheory.FrobStick
