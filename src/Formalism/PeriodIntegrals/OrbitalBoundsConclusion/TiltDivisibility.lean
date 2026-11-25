module

public import Formalism.PeriodIntegrals.ArtSch
import Supplements.MathlibImports.AnalysisAndTactics
public import GroundTheory.PAdicHodge.PerfectoidField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTilt

@[expose] public section

theorem tilt_divisibility : PI.ArtSch.TiltDiv :=
  @GlobalTheory.ArtinSchreierTilt.tiltDiv
