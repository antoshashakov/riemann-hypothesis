module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBlockParabolicSubgroupGL
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc


theorem _root_.GlobalTheory.T.card_blockParabolicSubgroupGL : ∀ (R : Type) [CommRing R] [Finite R] (a d : ℕ), a ≤ d →
    Nat.card (blockPar R a d) = Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  first | exact @GlobalTheory.StdLoc.card_blockPar | exact GlobalTheory.StdLoc.card_blockPar | (intros; apply GlobalTheory.StdLoc.card_blockPar <;> assumption)
