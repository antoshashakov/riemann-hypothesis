module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.compactness_statement : GlobalTheory.CompanionTheory.Jp.JpCmp := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp | exact GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp | (intros; apply GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp <;> assumption)
