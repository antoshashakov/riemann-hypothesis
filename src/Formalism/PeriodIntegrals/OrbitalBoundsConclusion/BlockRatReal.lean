module

public import Formalism.PeriodIntegrals.BlockRatReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.AntitoneStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.MapDetGenM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.NuOfAntitone
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem blockRatReal : PI.BlockRatReal.Stmt :=
  PI.BlockRatReal.stmt_of PI.BlockRatReal.UnitaryGroupMassFormula.evenStep PI.BlockRatReal.UnitaryGroupMassFormula.Odd.oddStep
