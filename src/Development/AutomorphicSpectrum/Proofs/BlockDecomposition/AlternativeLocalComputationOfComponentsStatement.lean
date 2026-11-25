module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponents
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.alternative_local_computation_of_components : GlobalTheory.CompanionTheory.Jp.JpIw → GlobalTheory.CompanionTheory.Jp.JpHgt → GlobalTheory.CompanionTheory.Jp.JpUnif → GlobalTheory.CompanionTheory.Jp.JpCmp → GlobalTheory.CompanionTheory.Jp.JpPos → GlobalTheory.CompanionTheory.Jp.JpCondition := by
  first | exact @GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps | exact GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps | (intros; apply GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps <;> assumption)
