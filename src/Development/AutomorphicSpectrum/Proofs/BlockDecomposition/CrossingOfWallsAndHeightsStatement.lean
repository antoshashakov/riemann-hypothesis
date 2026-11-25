module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeights
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.crossing_of_walls_and_heights : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.HtLip → PositivityTheory.RgEis.PiLocalization₂ → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Cross := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.cross | exact GlobalTheory.CompanionTheory.RgEisCross.cross | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.cross <;> assumption)
