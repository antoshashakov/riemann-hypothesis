module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapFirstProperty
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.norm_map_first_property : PositivityTheory.Rg.Tf.Loc.N1 := by
  first | exact @GlobalTheory.CompanionTheory.NormOnto.norm_onto | exact GlobalTheory.CompanionTheory.NormOnto.norm_onto | (intros; apply GlobalTheory.CompanionTheory.NormOnto.norm_onto <;> assumption)
