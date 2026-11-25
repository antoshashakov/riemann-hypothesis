module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInjectiveMatrixSpace
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory
open scoped Matrix

theorem _root_.GlobalTheory.T.fourier_injective_matrix_space : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ, Continuous g → Integrable g → (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness | exact GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness | (intros; apply GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness <;> assumption)
