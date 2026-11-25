module

public import Formalism.PeriodIntegrals.NUnimodLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.FrameC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.Transf
import Supplements.MathlibImports.AnalysisAndTactics
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.Development

@[expose] public section

theorem n_unimodular_local : PI.NUnimodLoc.NUnimodLoc :=
  PI.NUnimodLoc.UnitaryGroupMassFormula.nUnimodLoc_of PI.NUnimodLoc.UnitaryGroupMassFormula.FC.frame_conjugation_unimodular
    PI.NUnimodLoc.UnitaryGroupMassFormula.TR.transfer_holds
