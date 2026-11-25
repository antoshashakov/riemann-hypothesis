module

public import Formalism.PeriodIntegrals.SelfDualLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.LocBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.SelfDualLocOfLocBasis
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem self_dual_local : PI.SelfDualLoc :=
  PI.SelfDualLoc.W.selfDualLoc_of_locBasis PI.SelfDualLoc.W.locBasis
