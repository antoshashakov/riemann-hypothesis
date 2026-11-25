module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeThirdProperty
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.lattice_third_property : PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement → PositivityTheory.Rg.Tf.Loc.L1 → PositivityTheory.Rg.Tf.Loc.L3 := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset | exact GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset | (intros; apply GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset <;> assumption)
