module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseq
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.module_finite_limit_of_lseq : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W] (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  first | exact @GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | exact GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | (intros; apply GlobalTheory.CompanionTheory.TowerLim.module_finite_lim <;> assumption)
