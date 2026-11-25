module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Mathlib.RingTheory.Artinian.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianLimitLiftOfCompatible
import Supplements.MathlibImports.AnalysisAndTactics
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens

@[expose] public section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.artinian_limit_lift_of_compatible : ∀ (W : Type) [CommRing W] (S : Sys.{1} W), (∀ n, IsArtinian W (S.M n)) → ∀ (N : ∀ n, Submodule W (S.M n)) (y : ∀ n, S.M n), (∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) → (∀ n, S.r n (y (n + 1)) - y n ∈ N n) → ∃ z : S.lim, ∀ n, z.1 n - y n ∈ N n := by
  first | exact @GlobalTheory.CompanionTheory.ArtinTower.exists_compatible | exact GlobalTheory.CompanionTheory.ArtinTower.exists_compatible | (intros; apply GlobalTheory.CompanionTheory.ArtinTower.exists_compatible <;> assumption)
