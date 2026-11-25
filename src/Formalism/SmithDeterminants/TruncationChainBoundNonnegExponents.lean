module

public import Formalism.SmithDeterminants.StatementDVR
public import Formalism.SmithDeterminants.DivisibilityChains.SmithExists
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.A

theorem smithExists : SmithExists := smith_form_exists

end Formalism.A
