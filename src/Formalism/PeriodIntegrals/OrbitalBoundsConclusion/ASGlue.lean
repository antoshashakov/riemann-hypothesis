module

public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationGluing.ValbLeOfCoeffEqZero
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem tiltSurjectiveOfParts : PI.ArtSch.TiltGlue := PI.ArtSch.Glue.tiltGlue
