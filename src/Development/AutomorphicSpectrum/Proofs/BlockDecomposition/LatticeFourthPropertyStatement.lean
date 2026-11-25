module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFourthProperty
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.lattice_fourth_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.L4 := by
  first | exact @GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent | exact GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent | (intros; apply GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent <;> assumption)
