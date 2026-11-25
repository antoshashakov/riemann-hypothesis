module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.height_bound_statement : GlobalTheory.CompanionTheory.Jp.JpHgt := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt | exact GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt | (intros; apply GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt <;> assumption)
