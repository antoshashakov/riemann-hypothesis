module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveOnSubspaceOpen
import Formalism.LocalRingCardinality.DataHost
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.positive_on_subspace_open : ∀ (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε Z S} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn <;> assumption)
