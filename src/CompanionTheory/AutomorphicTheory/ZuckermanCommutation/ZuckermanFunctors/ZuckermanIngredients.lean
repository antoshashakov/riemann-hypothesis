module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.AdjFromApply
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.DecompositionOfInjective
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.LieAlgebraHomomorphism
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSumStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplittingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBoundStatement
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLaws
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialMatrixUnitFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadratic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategory
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHom
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferentialStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIsoStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace CompanionTheory.Zuck

theorem zuckerman_ingredients : Steps := by
  exact {
    infChar := CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
    decOfInj := decomposition_of_injective
    decOfTrace := _root_.GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace
    homCat := _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat
    okTriv := trivial_rep_admissible
    okVr := vector_rep_admissible
    okWedge := _root_.GlobalTheory.CompanionTheory.ZuckWedge.okWedge
    okTens := _root_.GlobalTheory.CompanionTheory.ZuckTens.okTens
    matHom := _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom
    uIso := GlobalTheory.T.UnitaryIso
    homLie := CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism
    casSplit := GlobalTheory.T.CasimirSplitting
    casDS := GlobalTheory.T.CasimirDiagonalSum
    wedgeInt := _root_.GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt
    wedgeQ := _root_.GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ GlobalTheory.T.StandardDifferential _root_.GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single
    schur := CompanionTheory.D.gk.FinalFormK.schur'
    adj := adj_of _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom
    multOne := multOne_of _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism GlobalTheory.T.CasimirSplitting GlobalTheory.T.StandardDifferential
      CompanionTheory.D.gk.FinalFormK.kerZero' trivial_rep_admissible vector_rep_admissible _root_.GlobalTheory.CompanionTheory.ZuckTens.okTens
    inj := CompanionTheory.D.gk.FinalFormK.injectivity_induction
    occ := CompanionTheory.D.gk.FinalFormK.occurrence_induction
    zuckH := _root_.GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds
    decTens := _root_.GlobalTheory.CompanionTheory.ZuckDecTens.decTens _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism trivial_rep_admissible
    toRaw := _root_.GlobalTheory.CompanionTheory.ZuckToRaw.toRaw
    count := GlobalTheory.T.CountingBound
  }

end CompanionTheory.Zuck
