module

public import Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds
import Formalism.MahlerMeasure.FinalD
public import Formalism.MahlerMeasure.MahlerMeasureProofs.WindowAP
public import Formalism.MahlerMeasure.MahlerMeasureProofs.WindowMeanAP
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem windowCountAP : WindowCountAP := window_count_progression
theorem discsDisjointAP : DiscsDisjointAP := root_discs_disjoint_progression
theorem windowMeanAP : WindowMeanAP := windowMeanAP_of windowCountAP discsDisjointAP
theorem windowFullAP : WindowFullAP := windowFullAP_of valuation_window_lower_bound windowMeanAP
end Formalism.GM.Top
