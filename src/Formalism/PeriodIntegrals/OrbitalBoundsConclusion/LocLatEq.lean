module

public import Formalism.PeriodIntegrals.LocLatEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.AvoidP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.CoreFgOfLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.EpNontrivial
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem eq_iff_locallyEq : PI.LocLatEq.Stmt :=
  PI.LocLatEq.W.locLatEq_of PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP
    (PI.LocLatEq.W.coreP_of_unitP_avoidP_intP PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP PI.LocLatEq.W.intP)
