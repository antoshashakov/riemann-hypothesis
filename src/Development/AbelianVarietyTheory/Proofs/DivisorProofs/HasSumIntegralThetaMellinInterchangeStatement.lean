module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchange
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.hasSum_integral_theta_mellin_interchange : ∀ (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ), (∀ j, ‖a j‖ ≤ C) → ∀ (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, p y ≤ 1) → (∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j))) → Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖) → HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y) (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.HeckeMellin.hasSum_integral_theta | exact GlobalTheory.HeckeMellin.hasSum_integral_theta | (intros; apply GlobalTheory.HeckeMellin.hasSum_integral_theta <;> assumption)
