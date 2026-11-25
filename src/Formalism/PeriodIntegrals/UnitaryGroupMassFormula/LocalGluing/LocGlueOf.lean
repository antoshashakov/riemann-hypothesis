module

public import Formalism.PeriodIntegrals.LocHerm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.ExistsIntegralMultiple
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.MemOfProjEqZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.RieszRepresentationHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.LocHerm.Glue

theorem locGlue_of (hO : PI.LocHerm.LocOProj) : PI.LocHerm.LocGlue :=
  locGlue_of_pair (pair_of rieszRepresentation_holds existsIntegralMultiple hO)

end PI.LocHerm.Glue
