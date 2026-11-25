module

public import Formalism.MahlerMeasure.Statement
public import Formalism.MahlerMeasure.MahlerMeasureProofs.DeterminantBlockLeadingTerm
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem detBlockLead : DetBlockLead := determinant_block_leading_term
end Formalism.GM.Top
