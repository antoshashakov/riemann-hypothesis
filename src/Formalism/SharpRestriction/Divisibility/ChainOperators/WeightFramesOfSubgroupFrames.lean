module

public import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinorSpanCompl
import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

theorem kw_of_cutSB (h : CutKW.KWsb) : CutKW.KW := h minor_span_complement

end Formalism.MainNotions.DIV.Lemmas
