module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalBase
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.dual_stacked_exceptional_base : GroundTheory.Heights₂.Heights.DualStackedExcBase.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.exc_base | exact GlobalTheory.CompanionTheory.Ar.Giv.exc_base | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.exc_base <;> assumption)
