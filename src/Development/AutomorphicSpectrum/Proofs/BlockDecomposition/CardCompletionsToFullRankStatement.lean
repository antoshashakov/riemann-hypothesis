module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCompletionsToFullRank
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.card_completions_to_full_rank : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntCols.card_completions | exact GlobalTheory.CompanionTheory.Jp.CntCols.card_completions | (intros; apply GlobalTheory.CompanionTheory.Jp.CntCols.card_completions <;> assumption)
