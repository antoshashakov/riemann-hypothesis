module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt
import Supplements.MathlibImports.AnalysisAndTactics
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.PlanarKernelBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.PolynomialGrowthIntegrals
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.SlowWeightBound

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem sub : SUB := quadraticSublevelDecay'

theorem ker : KER := planarKernelBound'

theorem slow : SLOW := slowWeightBound'

end ReciprocityTheory.ChartRestriction.DS.Xi
