module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusConjugationConditionsAdaptedKernelDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacobiOfClass
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexForms
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSideProperties
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelPairScalarsIsUnitTrueColumns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTransla
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundStandardSeriesInertPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
import Formalism.PeriodIntegrals.OrbJetBase
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PdvClose

theorem at_of_true_columns : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → t.Adapted → t.TopPinned → 3 ≤ B.host.splitBound → 5 ≤ K.dl1 → 4 ≤ K.dl2 → (∀ Ee : OrbitPlaces.Ent (I.rec7 l Z), OrbitPlaces.Shape (I.rec7 l Z) L Gi Ee ∧ ∀ u, ∀ j < B.R.m, ∀ s ∈ B.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * L.sc.a) → GlobalTheory.Pdv.At ex t.ent := by
  intro hAlg hG1 hCD hII B X I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC hAd hTop hsplit hdl1 hdl2 hSh
  have hDuty : GlobalTheory.Pdv.Duty t := _root_.GlobalTheory.Pdv.duty_of_std I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC
  have hHyp : t.Hyp := _root_.GlobalTheory.colSide_hyp _ L hT Gi Gl K Y cX ex t hDuty.col hTop
  have hInp : GlobalTheory.ThLoc.Inputs := _root_.GlobalTheory.ThLoc.inputs_of_algT hAlg
  have hHost := GlobalTheory.KerStd.HostInert.hostAt_inert hG1 hCD hII
  obtain ⟨P, Bf, hK, he⟩ := hEntC
  obtain ⟨t', hc', hf'⟩ := hDuty.forms
  obtain ⟨ep, be, hBe, h0⟩ := _root_.GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit
  refine ⟨⟨_root_.GlobalTheory.Pdv.unUnit_stdKer I hOk hPins l Z L hT Gi Gl K Y cX ex t hStd,
    GlobalTheory.PdvKm.kmapRat_kerEntC' t P Bf hK he hDuty.rk,
    _root_.GlobalTheory.KFiClose.kFi_of_tie _ L hT Gi Gl K Y cX ex t' hc' hf',
    _root_.GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns I hOk hPins l Z ex.lev⟩, ep, be, (fun _ _ => -1), h0,
    _root_.GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit ep be _, ?_,
    _root_.GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d hInp _ L hT Gi Gl K Y cX ex t hHyp hsplit ep be _,
    _root_.GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted hInp _ L hT Gi Gl K Y cX ex t hHyp hAd ep be _,
    (hSh _).1⟩
  exact _root_.GlobalTheory.OrbitBoundStdRec.orbit_bound_rec _ L Gi K _ (hSh _).1 (hSh _).2 hdl1 hdl2 hBe rfl

end GlobalTheory.PdvClose
