module

public import Formalism.PeriodIntegrals.WwInjective
public import Formalism.PeriodIntegrals.WwCauchyBinet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
