module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.block_index_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  first | exact @GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone | exact GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone | (intros; apply GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone <;> assumption)
