module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefConjTransposeMulSelfEqExpPolynomial
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_hermitian_exp_eq_conjTranspose_mul_poly : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g → ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  first | exact @GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | exact GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | (intros; apply GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial <;> assumption)
