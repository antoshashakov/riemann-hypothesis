module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.identity_tube_holds : PositivityTheory.RgEis.IdTube := by
  first | exact @GlobalTheory.CompanionTheory.Eis.idTube | exact GlobalTheory.CompanionTheory.Eis.idTube | (intros; apply GlobalTheory.CompanionTheory.Eis.idTube <;> assumption)
