module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceModPrimeOfPolarisationIdealTimesLattic
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugatePlaceCmField
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicMemFrameStabilizerOfLatticeTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportCongruenceOfFrameVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportOfPolarisationIdealTimesLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecSubMemLatticeCompletionOfLattice
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDual
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevKFrame

theorem levK_frame : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ βT : GL (Fin T.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βT ΛT → ∀ Pg : Finset (Formalism.L2.DIV.Pl D.host.E), (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) → (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) → ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C Lv ΛT hsd hAA βT hfr Pg hPg hJ k κ hk
  obtain ⟨-, hmov, κ', hκ', hc⟩ := hk
  have hmovT := _root_.GlobalTheory.LevMoveAA.isMov_of_isAA D C.X.Λ ΛT (fmt T k) hAA hmov
  have hSt := _root_.GlobalTheory.LevMov.finE_mem_St_of_isMov D T ΛT βT hfr k hmovT
  refine ⟨hSt, fun PP hPP => ?_⟩
  obtain ⟨PP', hPP', hcj⟩ := _root_.GlobalTheory.ConjPlace.exists_conj_place D PP
  have hI : ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ PP'.asIdeal := by
    rw [hPP']; exact hJ κ κ.2 κ' hκ' PP hPP
  have h1 := _root_.GlobalTheory.LevCong.cong_of_frame D C.X.Λ Lv.β Lv.𝔪 PP'.asIdeal Lv.β_mem Lv.β_span (hPP' ▸ hPg PP hPP) (fmt T k) κ' hI hmov hc
  have h2 := _root_.GlobalTheory.LevExt.mulVec_sub_mem_hatV D C.X.Λ (PP'.asIdeal • C.X.Λ) (fmt T k) h1
  obtain ⟨b, hb, h3⟩ := _root_.GlobalTheory.LevkLoc.congr_of_isAA D C.X.Λ ΛT PP'.asIdeal PP'.isPrime hAA (fmt T k) h2
  have h4 := _root_.GlobalTheory.LevRedTriv.redFn_eq_one_of_cong D T ΛT βT hfr k hSt PP' b hb h3
  exact _root_.GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj D T ΛT hsd βT hfr k hSt PP PP' hcj h4

end GlobalTheory.LevKFrame

end
