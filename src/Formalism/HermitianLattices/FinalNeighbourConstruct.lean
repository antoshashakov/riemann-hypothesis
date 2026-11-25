module

public import Formalism.HermitianLattices.GenusCovolBound
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetFinite
import Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace
public import Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.HermitianLatticesTheory

theorem final_isomAct : IsomAct := Formalism.HermitianLatticesTheory.isomAct
theorem final_genusBasic : GenusBasic := Formalism.HermitianLatticesTheory.genusBasic
theorem final_finIntermediate : FinIntermediate := Formalism.HermitianLatticesTheory.finIntermediate
theorem final_shortVectors : ShortVectors := Formalism.HermitianLatticesTheory.shortVectors
theorem final_isomOfTrace : IsomOfTrace := Formalism.HermitianLatticesTheory.isomOfTrace
theorem final_traceReal : TraceReal := Formalism.HermitianLatticesTheory.traceReal
theorem final_autFinite : AutFinite := Formalism.HermitianLatticesTheory.autFinite
theorem final_genusCovol : GenusCovol := Formalism.HermitianLatticesTheory.genusCovol
theorem final_classSetFinite : ClassSetFinite := Formalism.HermitianLatticesTheory.classSetFinite

end Formalism.HermitianLatticesTheory
