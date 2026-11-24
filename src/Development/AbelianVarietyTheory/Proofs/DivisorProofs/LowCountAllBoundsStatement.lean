module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowCountAllBounds
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.low_count_all_bounds : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality := by
  first | exact @GlobalTheory.LowCount.lowC_all | exact GlobalTheory.LowCount.lowC_all | (intros; apply GlobalTheory.LowCount.lowC_all <;> assumption)
