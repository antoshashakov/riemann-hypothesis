module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyExact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyNewton
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

theorem keyRep_of_start (hS : KeyStart) : KeyRep := keyRep_of hS keyNewton keyExact

end PI.UnitaryGroupMassFormula.UnimodLocStd
