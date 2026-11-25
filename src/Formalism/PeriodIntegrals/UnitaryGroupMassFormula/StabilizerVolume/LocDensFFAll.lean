module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFIn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFT
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.VolStabS

theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabS
