module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGeneric
import Formalism.LocalRingCardinality.DataHost
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rank_residue_le_rank_generic : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L] [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O), (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  first | exact @GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map | exact GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map | (intros; apply GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map <;> assumption)
