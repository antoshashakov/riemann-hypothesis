module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRpowDecayIsBigOCocompact
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory


theorem _root_.GlobalTheory.T.prod_rpow_decay_isBigO_cocompact' : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  first | exact @GlobalTheory.prod_rpow_decay_isBigO_cocompact | exact GlobalTheory.prod_rpow_decay_isBigO_cocompact | (intros; apply GlobalTheory.prod_rpow_decay_isBigO_cocompact <;> assumption)
