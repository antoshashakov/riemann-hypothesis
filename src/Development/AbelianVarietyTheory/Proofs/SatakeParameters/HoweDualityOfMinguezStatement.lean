module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguez
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.howe_duality_of_minguez : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.HoweDualityGL := by
  first | exact @GlobalTheory.HoweBridge.main | exact GlobalTheory.HoweBridge.main | (intros; apply GlobalTheory.HoweBridge.main <;> assumption)
