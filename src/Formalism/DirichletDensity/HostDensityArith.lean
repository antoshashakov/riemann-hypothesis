module

public import Formalism.DirichletDensity.Statement
public import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.HF.Final

theorem quadDiscr : Formalism.HF.QuadDiscr := Formalism.HF.quadDiscr
theorem mqDiscr : Formalism.HF.MQDiscr := Formalism.HF.mqDiscr_of quadDiscr

end Formalism.HF.Final
