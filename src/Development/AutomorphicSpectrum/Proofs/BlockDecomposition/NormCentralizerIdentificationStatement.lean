module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCentralizerIdentification
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.norm_centralizer_identification : PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 := by
  first | exact @GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma | exact GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma | (intros; apply GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma <;> assumption)
