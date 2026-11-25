module

public import Formalism.PeriodIntegrals.StdCharTR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardCharacterTrace.SumEmbeddingEqTrace
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem stdCharTR : PI.StdCharTR.Target :=
  PI.StdCharTRWork.stdCharTR_main
