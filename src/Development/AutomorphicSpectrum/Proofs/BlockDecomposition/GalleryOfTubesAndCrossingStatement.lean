module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossing
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.gallery_of_tubes_and_crossing : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.IdTube → PositivityTheory.RgEis.TubeChain → PositivityTheory.RgEis.Cross → PositivityTheory.RgEis.Gallery := by
  first | exact @GlobalTheory.CompanionTheory.RgEisGal.gallery | exact GlobalTheory.CompanionTheory.RgEisGal.gallery | (intros; apply GlobalTheory.CompanionTheory.RgEisGal.gallery <;> assumption)
