module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsos
import Supplements.MathlibImports.AnalysisAndTactics
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

@[expose] public section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls

theorem _root_.GlobalTheory.T.lseq_of_level_isos : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W) (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)), (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) → LSeq l S S' → Nonempty (LSeq l T T') := by
  first | exact @GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | exact GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | (intros; apply GlobalTheory.CompanionTheory.TowerSeq.lseq_transport <;> assumption)
