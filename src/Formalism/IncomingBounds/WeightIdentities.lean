module

public import Formalism.IncomingBounds.StatementThmP
public import Formalism.IncomingBounds.FlowDegreeBounds.Cayley
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaF
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
public import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.IncomingBounds

theorem lemmaFa : LemmaFa := strongDuality
theorem lemmaFc : LemmaFc := lemmaFc_of maxFlowValueAttained strongDuality
theorem incomingBound : IncomingBound := incomingBound_of maxFlowValueAttained strongDuality
theorem cayleyId : CayleyId := cayleyIdentity

end Formalism.IncomingBounds
