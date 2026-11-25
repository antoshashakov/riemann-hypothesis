module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanes
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  first | exact @GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | exact GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | (intros; apply GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes <;> assumption)
