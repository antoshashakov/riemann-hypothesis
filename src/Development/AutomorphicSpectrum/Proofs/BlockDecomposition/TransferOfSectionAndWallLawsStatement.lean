module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLaws
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.transfer_of_section_and_wall_laws : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgTransfer.transfer | exact GlobalTheory.CompanionTheory.RgTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgTransfer.transfer <;> assumption)
