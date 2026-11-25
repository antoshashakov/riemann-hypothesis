module

public import Formalism.PeriodIntegrals.AreaLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeArea.ImConjMulCombo
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem area_lattice_formula : PI.AreaLat := PI.AreaLatWork.areaLat
