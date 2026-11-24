module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHarmonicMonomialMulGaussianComplex
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

theorem _root_.GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex : ∀ (k : ℤ) (l : ℂ), 𝓕 (fun w : ℂ => GlobalTheory.HeckeTheta.hmon k w * Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l = (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (GlobalTheory.HeckeTheta.hmon k (l / 2) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian | exact GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian | (intros; apply GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian <;> assumption)
