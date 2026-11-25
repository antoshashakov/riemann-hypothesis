module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDet
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.parabolic_law_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisPar.parLaw | exact GlobalTheory.CompanionTheory.RgEisPar.parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisPar.parLaw <;> assumption)
