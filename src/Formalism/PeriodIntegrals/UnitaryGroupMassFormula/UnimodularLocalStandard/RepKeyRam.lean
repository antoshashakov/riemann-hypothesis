module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepKey
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

theorem keyStart_of_keyStartRam (hR : KeyStartRam) : KeyStart := keyStart_of_ram hR

theorem keyRep_of_ram (hR : KeyStartRam) : KeyRep := keyRep_of_start (keyStart_of_keyStartRam hR)

end PI.UnitaryGroupMassFormula.UnimodLocStd
