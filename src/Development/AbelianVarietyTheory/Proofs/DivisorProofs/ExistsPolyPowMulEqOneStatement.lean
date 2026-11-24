module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyPowMulEqOne
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_poly_pow_mul_eq_one' : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B → ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  first | (exact @GlobalTheory.exists_poly_pow_mul_eq_one) | (exact GlobalTheory.exists_poly_pow_mul_eq_one) | (intros; apply GlobalTheory.exists_poly_pow_mul_eq_one  <;> assumption)
