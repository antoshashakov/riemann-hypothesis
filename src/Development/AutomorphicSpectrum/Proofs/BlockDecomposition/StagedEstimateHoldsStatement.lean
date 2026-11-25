module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.staged_estimate_holds : PositivityTheory.RgEis.PiLocalization₂ := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.stage | exact GlobalTheory.CompanionTheory.RgEis.stage | (intros; apply GlobalTheory.CompanionTheory.RgEis.stage <;> assumption)
