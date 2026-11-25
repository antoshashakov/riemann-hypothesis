module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.positivity_statement : GlobalTheory.CompanionTheory.Jp.JpPos := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Pos.jpPos | exact GlobalTheory.CompanionTheory.Jp.Pos.jpPos | (intros; apply GlobalTheory.CompanionTheory.Jp.Pos.jpPos <;> assumption)
