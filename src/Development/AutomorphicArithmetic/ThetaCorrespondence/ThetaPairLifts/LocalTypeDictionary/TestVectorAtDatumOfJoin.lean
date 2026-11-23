module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatRowTest
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedDataOffBaseLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparatesLinB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedGridExistenceOfIdentity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftRowPropertiesConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerOfThetaMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleExistenceOfTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLinearBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalFactorRatioHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
open GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.LiteralAutomorphy GlobalTheory.Mem.R3.Rw.RowAt

private theorem rowChoices_of_grid (seed : GlobalTheory.RowEx.GridEx)
    (grids : ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → EvLgG (GridA c)) :
    ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → EvLgG (RowChoices c) := by
  obtain ⟨a, hSeed⟩ := seed
  obtain ⟨b, hGrid⟩ := grids
  refine ⟨max a b, fun c hc => ?_⟩
  have s := evG_of_ev (ev_scale fun eps _ => hSeed eps c (le_of_max_le_left hc))
  refine (s.inter (hGrid c (le_of_max_le_right hc))).imp fun K _ _ _ _ hv => ?_
  obtain ⟨⟨x, hx, init⟩, hg⟩ := hv
  refine hg.imp fun B f T _ grid w Z hX Wt z L hs hS hRec => ?_
  obtain ⟨hoff, hC, _, hξ⟩ := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z hX Wt z
  obtain ⟨G₀, _, _, _⟩ := init _ L (by rw [hs]) (by rw [hs]; exact hx) _ _ _ _ _ _ _ hS hoff
  have hAt : GridAt L.sc c (w.st Z) f (T.set f) := by
    rw [hs]
    exact grid _ _ _ _ _ _
  obtain ⟨G, _, W, M, ρ, ξ, cv, rm, S, rp, n, e, b, hI, hF, _⟩ :=
    hAt L rfl hRec _ _ _ _ _ _ _ hS hC hoff (fun t => ⟨_, hξ t, HEq.rfl⟩) G₀
  exact ⟨⟨_, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, b⟩, hI, rfl, hF⟩

theorem GlobalTheory.RowTestAssembly.test_vector_at_datum_of_grid : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate →
    (∃ c₀ : ℝ, ∀ c, c₀ ≤ c → EvLgG (GridA c)) → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun sg hw g P a12 K LM T3 grids =>
    have s1 := _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence sg P
    have s2 := _root_.GlobalTheory.SquareLM.twisted_square_local_matching hw P K LM
    have s3 := _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree P K LM
    have j := _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj P K LM s1 s2 s3
    have l := GlobalTheory.SqTop.lNe_of_functionalEquation a12.abs GlobalTheory.HeckeStrip.completedLBoundedInStrips GlobalTheory.SqTop.fieldDat
    atDat_rowTest_of_choices g P.cuspRapidDecay j.2.2.1
      (GlobalTheory.RowEx.injK_of_separates_linB T3 (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)))
      j.2.1 j.1 j.2.2.2.1 j.2.2.2.2
      (_root_.GlobalTheory.RowClaim.twisted_local_factor_ratio_holds P K LM j.2.1 l (_root_.GlobalTheory.SqTop.triEx_holds_alt hw P K LM l) (_root_.GlobalTheory.SqTower.tower_alt_bis P K LM l))
      (rowChoices_of_grid (GlobalTheory.RowEx.twisted_grid_existence_of_identity P) grids)
end
