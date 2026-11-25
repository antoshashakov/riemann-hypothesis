module

public import Formalism.PeriodIntegrals.WwCauchyBinet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem cauchy_binet_minors : PI.WwCauchyBinet.WwCauchyBinet := PI.WwCauchyBinetWork.wwCauchyBinet_main
