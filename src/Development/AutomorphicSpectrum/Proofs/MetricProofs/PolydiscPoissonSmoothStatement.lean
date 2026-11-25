module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmooth
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

theorem _root_.GlobalTheory.T.polydisc_poisson_smooth : ∀ (n : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℝ), 0 < ρ → Continuous (fun θ : Fin n → ℝ => h (torusPt ρ θ)) → ContDiffOn ℝ ∞ (polyPoisson ρ h) (Metric.ball 0 ρ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson <;> assumption)
