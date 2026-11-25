module

public import Formalism.CMTypeGalois.StatementField
public import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois
public import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField Ideal

namespace Formalism.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois

end Formalism.Q3
