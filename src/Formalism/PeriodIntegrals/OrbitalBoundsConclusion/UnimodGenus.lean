module

public import Formalism.PeriodIntegrals.UnimodGenus
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.UnimodLocalOfLocDual
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem unimodular_genus_unique : PI.UnimodGenus :=
  PI.UG.W.unimodGenus_of PI.UG.W.unimodLocal PI.UG.W.isomLocStd
