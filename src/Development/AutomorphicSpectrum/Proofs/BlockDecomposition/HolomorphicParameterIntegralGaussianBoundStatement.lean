module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicParameterIntegralGaussianBound
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory
open scoped Matrix

theorem _root_.GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ → (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) → ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ) → (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) → ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) → ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧ ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧ Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧ ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | exact GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | (intros; apply GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main <;> assumption)
