module

public import Formalism.MahlerMeasure.LevelSum
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelSum
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem levelAct : LevelAct := levelAct_of alternatingChooseSum
end Formalism.GM.Top
