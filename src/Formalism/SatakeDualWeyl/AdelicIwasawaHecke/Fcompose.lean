module

public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatake
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.UG.P

theorem satake_inert : Formalism.UG.SatakeInert := satake_transform_inert_prime exists_spherical_function_unitary

theorem satake_mul : Formalism.UG.SatMul := satake_transform_multiplicative exists_spherical_function_unitary

end Formalism.UG.P
