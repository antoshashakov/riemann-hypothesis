module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzQuadraticPhaseMultiplication
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped Matrix SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_quadratic_phase_multiplication : ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  first | exact @GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul | exact GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul | (intros; apply GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul <;> assumption)
