module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem hermRepUnram [Fact HermRepUnram] : HermRepUnram := Fact.out

theorem orthBasisPos : OrthBasisPos := orthBasisPos_holds

end Formalism.HermitianLattices.Ext.L3
