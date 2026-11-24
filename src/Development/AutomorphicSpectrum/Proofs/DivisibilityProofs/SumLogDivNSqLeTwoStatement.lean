module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivNSqLeTwo
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.sum_log_div_n_sq_le_two : ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) → ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.log_tail | exact GlobalTheory.CompanionTheory.Ar.Small.log_tail | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.log_tail <;> assumption)
