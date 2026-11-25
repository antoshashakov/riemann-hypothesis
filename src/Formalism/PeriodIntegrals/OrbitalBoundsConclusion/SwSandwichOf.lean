module

public import Formalism.PeriodIntegrals.SwSand
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.ChartZeroEqOneOfLongWeylSq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SideAUnrealifyRL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SideBUnrealifyRL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.UnrealifyRL
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem sandwich_of_chart : PI.SwSand.SandwichOf :=
  PI.SwSandwichOfWork.sandwichOf_of_charts PI.SwSandwichOfWork.normRL PI.SwSandwichOfWork.logG
    PI.SwSandwichOfWork.chartFwd PI.SwSandwichOfWork.chartBwd PI.SwSandwichOfWork.sideB
    PI.SwSandwichOfWork.sideA
