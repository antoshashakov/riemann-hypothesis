module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.eisenstein_scaling_law : PositivityTheory.RgEis.Scale := by
  first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)
