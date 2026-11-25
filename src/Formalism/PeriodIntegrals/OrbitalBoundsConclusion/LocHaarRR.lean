module

public import Formalism.PeriodIntegrals.LocHaarRR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.MemOrdR
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem local_haar_real_real : PI.LocHaarRR.Target := PI.LocHaarRRW.target
