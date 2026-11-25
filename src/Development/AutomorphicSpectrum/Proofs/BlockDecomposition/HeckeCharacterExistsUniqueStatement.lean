module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.hecke_character_exists_unique : PositivityTheory.Lbc.HeckeExistsUnique := by
  first | exact @GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | exact GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | (intros; apply GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique <;> assumption)
