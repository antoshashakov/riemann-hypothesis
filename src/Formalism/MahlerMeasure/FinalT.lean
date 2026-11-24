module

public import Formalism.MahlerMeasure.StatementT
public import Formalism.MahlerMeasure.MahlerMeasureProofs.BadCrit
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem badCrit : M.BadCrit := bad_criterion_holds
end Formalism.GM.Top
