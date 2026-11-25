module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaOrderOne
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_orderOne : GLOnto 1 ∧ GLCount 1 := by
  first | exact @GlobalTheory.PMonE.gl1 | exact GlobalTheory.PMonE.gl1 | (intros; apply GlobalTheory.PMonE.gl1 <;> assumption)
