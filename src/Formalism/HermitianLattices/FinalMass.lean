module

public import Formalism.HermitianLattices.StatementMass
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.HermitianLatticesTheory

theorem final_massBasic : MassBasic := Formalism.HermitianLatticesTheory.massBasic

end Formalism.HermitianLatticesTheory
