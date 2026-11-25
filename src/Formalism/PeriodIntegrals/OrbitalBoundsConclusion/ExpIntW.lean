module

public import Formalism.PeriodIntegrals.ExpIntW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.RootsOfUnityRingLeWittIntegers
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.StepIII
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem expIntegralWitt : PI.ExpIntW :=
  PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW
