module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityAsSumExpMinusOne
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.identity_as_sum_exp_minus_one : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ), (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  first | exact @GlobalTheory.ExpDivision.exists_division | exact GlobalTheory.ExpDivision.exists_division | (intros; apply GlobalTheory.ExpDivision.exists_division <;> assumption)
