module

public import Formalism.PeriodIntegrals.IdealLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.OKArea
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem ideal_lattice_basis : PI.IdealLattice :=
  PI.IdealLatticeWork.idealLattice_of PI.IdealLatticeWork.okArea PI.IdealLatticeWork.idealBasis
