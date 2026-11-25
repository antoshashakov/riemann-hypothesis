module

public import Formalism.PeriodIntegrals.LongWeylElementSquare
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BigCellConjugation.Monomial
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem big_cell_g : PI.SwBig.BigCellG := PI.SwBig.BigCellGProof.bigCellG
