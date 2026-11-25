module

public import Formalism.PeriodIntegrals.ProdFormulaE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormTraceLeOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ProdFormulaEOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.SumLocalTrace
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace PI.ProdFormulaE.Assemble

theorem prodFormulaE_of_haar (hH : St.HaarAlg) : PI.ProdFormulaE.ProdFormulaE :=
  Top.prodFormulaE_of hH modulus_eq_finitePlace Tr.sumLocalTrace TrIntP.norm_trace_le_one ResCharP.eq_iff_mem_asIdeal

end PI.ProdFormulaE.Assemble
