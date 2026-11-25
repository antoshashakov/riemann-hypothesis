module

public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmallArtinSchreier.ExistsAsOfValLtOne
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem smallSurjective : PI.ArtSch.TiltSmall := PI.UnitaryGroupMassFormula.ASSmall.tiltSmall
