module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupport
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.unipotent_hecke_support : PositivityTheory.Rg.Tf.Loc.QuotientIntegralCompactOpen := by
  first | exact @GlobalTheory.CompanionTheory.QuotU.h2U | exact GlobalTheory.CompanionTheory.QuotU.h2U | (intros; apply GlobalTheory.CompanionTheory.QuotU.h2U <;> assumption)
