module

public import Formalism.PeriodIntegrals.WeylProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylProduct.WeylProd
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem weyl_product_formula : PI.WeylProd := PI.WeylProdWork.weylProd
