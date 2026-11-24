module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegree
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.kaehler_rank_transcendence_degree : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (I : Type) [Fintype I] (u : I → L),
    AlgebraicIndependent K u → IntermediateField.adjoin K (Set.range u) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | exact GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | (intros; apply GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top <;> assumption)
