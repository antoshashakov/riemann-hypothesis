module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant
import Supplements.MathlibImports.AnalysisAndTactics
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.points_integral_zero_of_locally_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e), (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst <;> assumption)
