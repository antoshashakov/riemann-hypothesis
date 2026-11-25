module

public import Formalism.PeriodIntegrals.LocHerm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocOProj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem local_hermitian_glue : PI.LocHerm.LocGlue :=
  PI.LocHerm.Glue.locGlue_of projectiveOverOrder
