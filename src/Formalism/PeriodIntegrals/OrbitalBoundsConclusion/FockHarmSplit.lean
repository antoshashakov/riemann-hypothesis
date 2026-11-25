module

public import Formalism.PeriodIntegrals.FockDegreeTwoParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.MinusPartOfMem
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem harmonicSplitting_holds : PI.FockDegreeTwoParts.HarmSplit := PI.FHS.harmSplit
