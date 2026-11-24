module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DigitsSumLeLogb
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.digits_sum_le_mul_logb : ∀ (p n : ℕ), p.Prime → (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  first | exact @GlobalTheory.digits_sum_le_logb | exact GlobalTheory.digits_sum_le_logb | (intros; apply GlobalTheory.digits_sum_le_logb <;> assumption)
