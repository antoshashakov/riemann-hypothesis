module

public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittCoefficients.CoeffEqOfSubMem
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem witt_lift : PI.ArtSch.WittLift := PI.ArtSch.WittLiftWork.wittLift
