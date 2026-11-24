module

public import Formalism.MahlerMeasure.HasOrder
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem gamDeg : M.GamDeg := gamma_degree_bound
theorem gamLead : M.GamLead := gamma_leading_term
end Formalism.GM.Top
