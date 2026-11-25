module

public import Formalism.PeriodIntegrals.ProdFormulaE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarAlg
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem product_formula_e : PI.ProdFormulaE.ProdFormulaE :=
  PI.ProdFormulaE.Assemble.prodFormulaE_of_haar PI.ProdFormulaE.HaarAlgP.haarScaling
