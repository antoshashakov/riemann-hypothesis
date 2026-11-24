module

public import Formalism.PeriodIntegrals.ScGapBig
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SpectralGapLarge.ScGapBigMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem scGapBig : PI.ScGapBig.ScGapBig := PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
