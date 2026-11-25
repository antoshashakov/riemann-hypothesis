module

public import Formalism.FockGram.StatementLat
public import Formalism.FockGram.StatementHerm
public import Formalism.FockGram.FockGramProofs.HermDualOf
public import Formalism.FockGram.FockGramProofs.SubIndexNorm
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.E

theorem subIndexNorm : SubIndexNorm := indexEqNormDet

theorem hermDual : HermDual := hermDual_of subIndexNorm

end Formalism.E
