module

public import Formalism.PeriodIntegrals.LocFramePrim
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.DiffLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.DualFunctionalsExist
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem locFramePrim : PI.LocFramePrim.Statement :=
  PI.LocFramePrimWork.Steps_top PI.LocFramePrimWork.localDifferentPowerSpan PI.LocFramePrimWork.dualFunctionalsExist
    PI.LocFramePrimWork.primitiveOfDualFunctionals
