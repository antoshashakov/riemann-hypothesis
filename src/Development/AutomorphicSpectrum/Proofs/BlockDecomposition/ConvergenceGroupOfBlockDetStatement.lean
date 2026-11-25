module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDet
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.convergence_group_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ConvGrOf := by
  first | exact @GlobalTheory.CompanionTheory.Plucker.convGrOf | exact GlobalTheory.CompanionTheory.Plucker.convGrOf | (intros; apply GlobalTheory.CompanionTheory.Plucker.convGrOf <;> assumption)
