module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecay
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProdu
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainSpannedParamsOfValueIndependent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferred
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParams
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjoint
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpwardThetaLiftNeZeroOfLValueNeZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HeckeFormOfDoubling
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

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EvenOnto
theorem even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  intro hHC hCusp hDS hHCM hCW hHowe hWeil hSW hSWc hDoub hUnr D
  have hHecke := _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' hWeil hCusp hSW hSWc hDoub hUnr D
  obtain ⟨hFin, hMet⟩ := _root_.GlobalTheory.EvenMetric.finDim_and_metEx hHC hCusp D
  obtain ⟨hEig, hPoV, hInd⟩ := _root_.GlobalTheory.EvenOnto.eig_parOfVal_indep hCusp D hFin hMet
  have hBd := _root_.GlobalTheory.EvenOnto.parBound_of_rapidDecay hCusp D
  obtain ⟨hSpan, hAdj⟩ := _root_.GlobalTheory.EvenOnto.UpLift.upSpan_upAdj hDS hHCM hCusp hCW D
  have hPar := _root_.GlobalTheory.EvenOnto.upPar_of_transfer hCusp hHowe D
  have hRZ := _root_.GlobalTheory.EvenOntoRealZeta.realZeta hDS hHCM D
  have hZN := _root_.GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real D hMet hRZ
  have hNe := _root_.GlobalTheory.EvenOnto.upNe_of_heckeForm D hHecke hMet hZN
  have hStep := _root_.GlobalTheory.EvenOnto.stepUp D hFin hPoV hSpan hAdj hPar hNe
  exact _root_.GlobalTheory.EvenOnto.ontoAll_of D hFin hMet hEig hInd hBd hStep
end GlobalTheory.EvenOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  first | exact @_root_.GlobalTheory.EvenOnto.even_surjective_of_representatives | exact _root_.GlobalTheory.EvenOnto.even_surjective_of_representatives | (intros; apply _root_.GlobalTheory.EvenOnto.even_surjective_of_representatives <;> assumption)
end
