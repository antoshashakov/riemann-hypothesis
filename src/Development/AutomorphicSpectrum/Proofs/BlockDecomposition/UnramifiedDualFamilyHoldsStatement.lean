module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.unramified_dual_family_holds : PositivityTheory.Rg.Tf.Loc.IntegralBasisUnramified → PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement := by
  first | exact @GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family | exact GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family | (intros; apply GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family <;> assumption)
