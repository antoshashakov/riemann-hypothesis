module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthProperty
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.unipotent_hecke_fourth_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.T0 → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.MeasureTransportOpenSet := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.transport_open_trace | exact GlobalTheory.CompanionTheory.TfLoc.transport_open_trace | (intros; apply GlobalTheory.CompanionTheory.TfLoc.transport_open_trace <;> assumption)
