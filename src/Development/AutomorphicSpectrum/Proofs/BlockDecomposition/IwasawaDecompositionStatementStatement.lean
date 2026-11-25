module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.iwasawa_decomposition_statement : GlobalTheory.CompanionTheory.Jp.JpIw := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Iw.jpIw | exact GlobalTheory.CompanionTheory.Jp.Iw.jpIw | (intros; apply GlobalTheory.CompanionTheory.Jp.Iw.jpIw <;> assumption)
