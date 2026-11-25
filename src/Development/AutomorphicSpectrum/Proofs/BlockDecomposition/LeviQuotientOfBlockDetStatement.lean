module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviQuotientOfBlockDet
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.levi_quotient_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.LeviQ := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ | exact GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ | (intros; apply GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ <;> assumption)
