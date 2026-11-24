module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StWWFibrePoly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMoment
import Supplements.MathlibImports.AnalysisAndTactics
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.sphere_pair_log_sine_moment : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ),
    ∫ p : ℂ × ℂ, logSin 1 p.1 p.2 * (wS p.1 * wS p.2 * ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)] Q)) =
      Real.pi ^ 2 * ℓ (momentPoly (sphereMeasure.prod sphereMeasure) wwLogWeight
        (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment <;> assumption)
