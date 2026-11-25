module

import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.MoebiusJetDuality.StatementU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
public import Mathlib.Data.Fintype.Defs

@[expose] public section

noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

variable {ι : Type} [Fintype ι] {p q : ℕ}

end GlobalTheory.HodgeDomain
