module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfLintegralSmoothEq
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.measure_eq_of_lintegral_smooth_eq' : ∀ (N : ℕ) (m₁ m₂ : Measure (Fin N → ℝ)) [IsFiniteMeasureOnCompacts m₂], (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂) → m₁ = m₂ := by
  first | exact @GlobalTheory.measure_eq_of_lintegral_smooth_eq | exact GlobalTheory.measure_eq_of_lintegral_smooth_eq | (intros; apply GlobalTheory.measure_eq_of_lintegral_smooth_eq <;> assumption)
