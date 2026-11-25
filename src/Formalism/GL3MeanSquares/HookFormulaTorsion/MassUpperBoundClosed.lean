module

public import Formalism.GL3MeanSquares.MassLowerBoundClosed
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField Finset

namespace Formalism.HermitianLattices.SiegelMassBounds

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem siegel_mass_ratio : SiegelMassRatioThm := Formalism.HermitianLattices.Ext.L3.siegelMassRatio

end Formalism.HermitianLattices.SiegelMassBounds
