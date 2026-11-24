module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantLinearFunctional
import Supplements.MathlibImports.AnalysisAndTactics
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.mixed_discriminant_linear_functional : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
    ∃ L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ, ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional <;> assumption)
