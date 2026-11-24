module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionDiagonalIdentity
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.partial_fraction_diagonal_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, d i - pfX d d' + ∑ j, pfR d d' j / (d i - d' j) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHe.Frame.pfZero | exact GlobalTheory.CompanionTheory.RgHe.Frame.pfZero | (intros; apply GlobalTheory.CompanionTheory.RgHe.Frame.pfZero <;> assumption)
