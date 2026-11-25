module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqPairGlue
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqPairLocal
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem split_pair_generation : Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen := square_pair_glue square_pair_local
