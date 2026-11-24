module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMomentPower
import Supplements.MathlibImports.AnalysisAndTactics
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.sphere_moment_power : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one <;> assumption)
