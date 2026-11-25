module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.uniform_boundedness_statement : GlobalTheory.CompanionTheory.Jp.JpUnif := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Unif.jpUnif | exact GlobalTheory.CompanionTheory.Jp.Unif.jpUnif | (intros; apply GlobalTheory.CompanionTheory.Jp.Unif.jpUnif <;> assumption)
