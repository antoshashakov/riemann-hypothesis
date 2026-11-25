module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankLowerLeftEqLowerRight
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.card_rank_lower_left_eq_lower_right : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank | exact GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank | (intros; apply GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank <;> assumption)
