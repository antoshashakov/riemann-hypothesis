module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOfImmersionComposition
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

@[expose] public section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.analytic_of_immersion_composition : ∀ {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V) (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ), AnalyticAt ℂ ψ (F y₀) → (fderiv ℂ ψ (F y₀)).ker = ⊥ → AnalyticAt ℂ H y₀ → ContinuousAt F y₀ → (∀ᶠ y in nhds y₀, ψ (F y) = H y) → AnalyticAt ℂ F y₀ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion | exact GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion | (intros; apply GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion <;> assumption)
