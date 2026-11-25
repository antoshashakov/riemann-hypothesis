module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLt
import Formalism.LocalRingCardinality.DataHost
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
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


theorem _root_.GlobalTheory.T.summable_denominator_power_of_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow <;> assumption)
