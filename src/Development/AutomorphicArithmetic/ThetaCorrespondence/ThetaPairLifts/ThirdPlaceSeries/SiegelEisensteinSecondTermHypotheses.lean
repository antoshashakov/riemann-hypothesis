module

public import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Prm1
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowRatWOfRowTest
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EvaluationGridOfJoin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FunctionalsSeparateOfHoweUnramOfSiegelWeil
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TestVectorAtDatumOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.At23OfAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FourierCoefficientFitOfJoin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypothesesNonemptyOfUnramifiedExponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedBundlesL3OfOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenAndLinkedOfStrongerExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenOrbitOfUnramifiedExponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowFunAtGridA
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SurjectiveAndLowWeightOfUnramifiedExponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopPlug
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.Lit
open UpperTheory.Top
theorem nonempty_hyps_definite_side_of_closed_bound : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.CovTop.CovolumeBoundOfX → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), (∀ cDep : ℝ, _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) → Nonempty (_root_.GlobalTheory.Fc.HypsAlt S0.NL _root_.GlobalTheory.Fc.DefiniteSideCondition) := by
  intro P F hA hM hX hL hN
  have C := P.litN
  have hS :=
    UpperTheory.Lit.functionalsSeparate_of_howeUnram_of_siegelWeil F GlobalTheory.Hk3.howeUnram_holds P.siegelWeilUnitaryConvergent
  have hFit := GlobalTheory.BigTop.Fun.Close.fourier_coefficient_fit_of_join_alt F C.join C.fe hA hM hS (GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses' P).2
  have grids := GlobalTheory.Mem.LiteralAutomorphy.evaluation_grid_of_join F.howeDualityReal hM F C.join C.fe hA
    (GlobalTheory.WeilConv.twisted_weil_representation_convergence F.siegelSetUnitary F) (GlobalTheory.T.twisted_local_factors_match F.howeDualityReal F hA hM)
    (GlobalTheory.T.twisted_square_theta_integrals_eq F hA hM) hS
  have hRat := GlobalTheory.Mem.LiteralAutomorphy.rowRatW_of_rowTest (GlobalTheory.RowTestAssembly.test_vector_at_datum_of_grid F.siegelSetUnitary F.howeDualityReal
    P.greenCuspidal F C.fe hA hM hS grids)
  obtain ⟨CF1, hCF1⟩ := grids
  obtain ⟨CF0, hCF0⟩ := GlobalTheory.Fc.StageOne.rowFun_at_gridA_alt P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay P.casselmanWallach
    P.rayClassFieldSt hFit
  let c := max CF0 CF1
  let origin := GlobalTheory.HeightCounting.Up.extensionWithOrigin hL c
  let ext := extensionWithAtProperty hL origin (GridA c)
  have hOpen := (GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt hL
    (GlobalTheory.HeightCounting.Up.extensionWithList hL c) ext SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)).2 (GlobalTheory.T.open0_of_unitary_group_hypotheses P hL c)
  exact S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt P hRat hL c (GridA c)
    (hCF1 c (le_max_right _ _)) (hN c)
    (hCF0 c (le_max_left _ _) hL origin SExt.none (geoCl anyGeometry)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩) hOpen)
    (GlobalTheory.Glob.CovolRow.linked_bundles_l3_of_open_alt P.discreteSeriesCover P.harishChandraModules
      P.cuspRapidDecay P.casselmanWallach P.rayClassFieldSt hX hL ext SExt.none (geoCl anyGeometry)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1.1⟩) hOpen)
theorem every_character_of_theta_integrals_local_matching (P : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses) (F : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hX : _root_.GlobalTheory.CovTop.CovolumeBoundOfX) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hV : VWin) :
    UpperTheory.EveryCharacter :=
  _root_.UpperTheory.Top.every_character_of_green_v_win (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) hV
    (_root_.UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL fun cDep => _root_.UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
end UpperTheory.Lit
end
end
