module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOverLatticeQuotientLocallyConstant
import Formalism.LocalRingCardinality.DataHost
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.summable_over_lattice_quotient_locally_constant : ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic | exact GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic <;> assumption)
