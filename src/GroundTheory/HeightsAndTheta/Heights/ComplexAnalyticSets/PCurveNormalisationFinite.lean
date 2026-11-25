module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsNoetherIntegralClosure
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveNormalisationFinite.proof (hN : FieldNumbers.NoetherIntegralClosureFinite.Statement.{0}) :
    CurveNormalisationFinite.Statement := by
  intro n I q hI
  have := isReduced_curveLocalRing I q hI
  exact finite_integralClosure_of_isReduced hN (algebraMap _ (curveLocalRing I q)) (curveLocalRing_eq_div I q)

end GroundTheory.Heights₂.Heights
