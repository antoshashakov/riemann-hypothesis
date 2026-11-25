module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtCoordinateCauchyIntegral
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.differentiableAt_coordinate_cauchy_integral : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  first | exact @GlobalTheory.cauchyCoord_differentiableAt | exact GlobalTheory.cauchyCoord_differentiableAt | (intros; apply GlobalTheory.cauchyCoord_differentiableAt <;> assumption)
