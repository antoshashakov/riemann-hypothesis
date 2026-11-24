module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.FourierTransform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEq
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent

@[expose] public section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.fourier_lipschitzOneVariableKernel_eq : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ), 𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  first | exact @GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | exact GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | (intros; apply GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow <;> assumption)
