module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrBase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.InjectiveOfLinearIndependent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.T2SpaceOfIsValuativeTopology
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.ProdFormulaE.Tr

theorem sumLocalTrace : TrSum := trSum_of toPi_injective toPi_surjective

end PI.ProdFormulaE.Tr
