module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierOneParameterIntegral
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory


theorem _root_.GlobalTheory.T.fourier_one_parameter_integral : ∀ (A : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A), Continuous c → ∀ (F G : A → ℂ), Continuous F → Continuous G → Integrable F lam → Integrable G lam → ∀ (χ : AddChar A ℂ), Continuous χ → (∀ x, ‖χ x‖ = 1) → ∀ (f : ℝ), (∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ)))) → (∀ (b : A) (s : ℝ), HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) → ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt | exact GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt | (intros; apply GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt <;> assumption)
