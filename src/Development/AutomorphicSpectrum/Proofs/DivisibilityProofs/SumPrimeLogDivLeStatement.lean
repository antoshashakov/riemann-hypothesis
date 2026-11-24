module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumPrimeLogDivLe
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.sum_prime_log_div_le : ∀ x : ℝ, 1 ≤ x → ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + Real.log 4 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four | exact GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four <;> assumption)
