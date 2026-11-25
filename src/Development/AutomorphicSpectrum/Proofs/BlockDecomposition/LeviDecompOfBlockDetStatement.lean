module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDet
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.levi_decomp_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.LeviS := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLevi.leviS | exact GlobalTheory.CompanionTheory.RgEisLevi.leviS | (intros; apply GlobalTheory.CompanionTheory.RgEisLevi.leviS <;> assumption)
