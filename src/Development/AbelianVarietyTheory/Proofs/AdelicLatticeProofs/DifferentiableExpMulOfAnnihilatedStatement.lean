module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableExpMulOfAnnihilated
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.differentiable_exp_mul_of_annihilated' : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by
  first | exact @GlobalTheory.differentiable_exp_mul_of_annihilated | exact GlobalTheory.differentiable_exp_mul_of_annihilated | (intros; apply GlobalTheory.differentiable_exp_mul_of_annihilated <;> assumption)
