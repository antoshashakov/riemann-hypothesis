module

public import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformRestrictionStatementHolds
import Supplements.MathlibImports.AnalysisAndTactics
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.uniform_restriction_statement_holds : UnifRestrictStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.unifRestrict | exact GlobalTheory.CompanionTheory.Ar.Giv.unifRestrict | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.unifRestrict <;> assumption)
