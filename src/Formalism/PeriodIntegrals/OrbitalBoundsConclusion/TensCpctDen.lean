module

public import Formalism.PeriodIntegrals.FinOrdAd
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdCpctDen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactTensorDensity.TensCpctDenOf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem tensor_compact_dense : PI.TensCpctDen := PI.tensCpctDen_of compactBounded
