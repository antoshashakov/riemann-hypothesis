module

public import Formalism.PeriodIntegrals.LatLocGlob
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalLattice.ExistsSmulMemOfLocal
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem latLocGlob : PI.LatLocGlob.LatLocGlob := PI.LatLocGlob.Proof.latLocGlob_core
