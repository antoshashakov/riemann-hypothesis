module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantTwoRowExpansion
import Supplements.MathlibImports.AnalysisAndTactics
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.mixed_discriminant_two_row_expansion : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (u : Fin (d + 2) → Fin 2 → ℝ) (v : Fin (d + 2) → ℝ) (n₀ n₁ : Fin 3 → ℝ) (e₀ e₁ : ℂ),
      ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁)
        ((∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))) =
      e₀ * e₁ * L (evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two <;> assumption)
