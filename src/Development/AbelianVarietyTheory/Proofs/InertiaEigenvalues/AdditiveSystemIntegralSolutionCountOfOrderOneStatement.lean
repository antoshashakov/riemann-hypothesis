module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSolutionCountOfOrderOne
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  first | exact @GlobalTheory.PMonE.LinCount.glCount_of_one | exact GlobalTheory.PMonE.LinCount.glCount_of_one | (intros; apply GlobalTheory.PMonE.LinCount.glCount_of_one <;> assumption)
