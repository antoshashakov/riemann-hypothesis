module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFirstProperty
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.lattice_first_property : PositivityTheory.Rg.Tf.Loc.L1 := by
  first | exact @GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff | exact GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff | (intros; apply GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff <;> assumption)
