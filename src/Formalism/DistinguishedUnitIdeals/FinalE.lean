module

public import Formalism.DistinguishedUnitIdeals.StatementE
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.BaseGamC
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.RhoMapFunctorial
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.SplittingOfPositiveLevel
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.ExponentWindows.E

theorem theorem_E_assembled : ThmEAssembly :=
  thmE_of rho_map_exists rho_map_linear rho_map_functorial splitting_of_extension

end Formalism.ExponentWindows.E
