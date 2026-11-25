module

public import Formalism.PeriodIntegrals.FlagGramNonneg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.Gval
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem flag_gram_nonneg : PI.FlagGramNonneg := PI.UnitaryGroupMassFormula.FlagGramNonneg.main
