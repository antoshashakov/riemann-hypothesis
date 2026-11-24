module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNullModP
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.pullback_cone_null_mod_p_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | exact GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP <;> assumption)
