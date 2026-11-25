module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapTorusSurjective
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.norm_map_torus_surjective : PositivityTheory.Rg.Tf.Loc.T0 := by
  first | exact @GlobalTheory.CompanionTheory.LocTop.t0 | exact GlobalTheory.CompanionTheory.LocTop.t0 | (intros; apply GlobalTheory.CompanionTheory.LocTop.t0 <;> assumption)
