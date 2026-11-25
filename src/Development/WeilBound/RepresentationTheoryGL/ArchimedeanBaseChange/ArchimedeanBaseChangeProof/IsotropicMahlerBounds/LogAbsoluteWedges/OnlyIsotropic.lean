module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisG
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTermOfIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightSupportBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparison
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler
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

namespace PositivityTheory.Rg.BcB.D1

theorem mulF : MulF := _root_.GlobalTheory.CompanionTheory.WedgeMinor.mulF
theorem detMono : DetMono := _root_.GlobalTheory.CompanionTheory.DetMonotone.detMono
theorem mulI : MulI := _root_.GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono detMono
theorem wedgeF : WedgeF := _root_.GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF mulF
theorem wedgeI : WedgeI := _root_.GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI detMono mulI
theorem wedgeSub : WedgeSub := _root_.GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub
theorem pairF : PairF := _root_.GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF mulF
theorem pairI : PairI := _root_.GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono detMono
theorem logAbsBasic : LogAbsBasic := _root_.GlobalTheory.CompanionTheory.LogAbs.logAbsBasic
theorem szFin : SzFin := _root_.GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin
theorem finSupp : FinSupp := _root_.GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul mulF mulI szFin
theorem degAdelic : DegAdelic := _root_.GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of mulF mulI logAbsBasic finSupp
theorem degBasisG : DegBasisG := _root_.GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of wedgeF wedgeI mulF mulI logAbsBasic finSupp
theorem degBasis : DegBasis := _root_.GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG degBasisG
theorem degSubmod : DegSubmod := _root_.GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of wedgeF wedgeI wedgeSub finSupp degBasisG _root_.GlobalTheory.CompanionTheory.LinAlg.twoBases
theorem degRat : DegRat := _root_.GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG degBasisG
theorem degMove : DegMove := _root_.GlobalTheory.CompanionTheory.DegMoveProof.degMove_of mulF mulI szFin finSupp degBasisG
theorem degBdd : DegBdd := _root_.GlobalTheory.CompanionTheory.DegBound.degBdd_of wedgeF wedgeI mulF mulI szFin finSupp logAbsBasic degBasisG
theorem conjPlaces : ConjPlaces := _root_.GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces
theorem sizeBasic : SizeBasic := _root_.GlobalTheory.CompanionTheory.Size.sizeBasic szFin conjPlaces
theorem degPairing : DegPairing :=
  _root_.GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of wedgeF wedgeI mulF mulI pairF pairI szFin finSupp logAbsBasic conjPlaces degBasisG _root_.GlobalTheory.CompanionTheory.RadicalForm.radical
theorem mahler_of_c (h : MahlerC) : Mahler := _root_.GlobalTheory.CompanionTheory.Cutoff.mahler_of degBdd degRat h
theorem mahler : Mahler := mahler_of_c (PositivityTheory.Rg.BcB.E1.mahlerC_of_deg degBasis degAdelic degBdd degRat)
theorem onlyStable : OnlyStable := _root_.GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of degSubmod degMove degBdd degPairing sizeBasic
theorem onlyIsotropic : OnlyIsotropic := _root_.GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of onlyStable degPairing sizeBasic
theorem ellTerm : EllTerm := _root_.GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic onlyIsotropic
theorem chainSum : ChainSum := fun m =>
  ⟨_root_.GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator m, _root_.GlobalTheory.CompanionTheory.SignChain.gam_support m, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).1, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).2.1, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).2.2⟩

end PositivityTheory.Rg.BcB.D1
