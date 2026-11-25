module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemSurjectivityAndCountOrderZero
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero : GLOnto 0 ∧ GLCount 0 := by
  first | exact @GlobalTheory.PMonE.glOnto_zero_and_glCount_zero | exact GlobalTheory.PMonE.glOnto_zero_and_glCount_zero | (intros; apply GlobalTheory.PMonE.glOnto_zero_and_glCount_zero <;> assumption)
