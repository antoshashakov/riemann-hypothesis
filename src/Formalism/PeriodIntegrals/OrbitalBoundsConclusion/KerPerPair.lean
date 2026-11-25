module

public import Formalism.PeriodIntegrals.KerLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PeriodPairIndependence.IndepOfImNe
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem exists_periodPairOfIdeal : PI.KerLat.PerPair := PI.KerLat.PerPairProof.perPair
