module

public import Formalism.PeriodIntegrals.OkpInert
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.OkpInertMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem integers_inert_prime : PI.OkpInert := PI.OkpW.okpInert_main
