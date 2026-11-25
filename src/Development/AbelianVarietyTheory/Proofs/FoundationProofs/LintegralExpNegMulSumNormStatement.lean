module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralExpNegMulSumNorm
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.lintegral_exp_neg_mul_sum_norm_matrix : ∀ (p q : ℕ) (b : ℝ), 0 < b → ∫⁻ B : Fin p → Fin q → ℂ, ENNReal.ofReal (Real.exp (-(b * ∑ i, ∑ j, ‖B i j‖))) = ENNReal.ofReal ((2 * Real.pi / b ^ 2) ^ (p * q)) := by
  first | exact @GlobalTheory.CartanInt.lintegral_exp_neg_mul_sum_norm | exact GlobalTheory.CartanInt.lintegral_exp_neg_mul_sum_norm | (intros; apply GlobalTheory.CartanInt.lintegral_exp_neg_mul_sum_norm <;> assumption)
