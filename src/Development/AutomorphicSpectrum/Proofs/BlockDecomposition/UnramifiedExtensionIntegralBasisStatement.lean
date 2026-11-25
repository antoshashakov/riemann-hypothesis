module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.unramified_extension_integral_basis : PositivityTheory.Rg.Tf.Loc.D0a := by
  first | exact @GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | exact GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | (intros; apply GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a <;> assumption)
