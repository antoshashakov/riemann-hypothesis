module

public import Formalism.PeriodIntegrals.SqPair
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.SqPairGlueMain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem square_pair_glue : PI.SqPair.PLocalAll → Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen :=
  PI.SqPairW.sqPairGlue_main
