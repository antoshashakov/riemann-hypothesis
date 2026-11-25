module

public import Formalism.PeriodIntegrals.RTTIndependence
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuarticIndependence.QmIndep
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem rtt_independence' : PI.RTTIndependence := PI.QmIndepW.qmIndep
