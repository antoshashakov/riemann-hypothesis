module

public import Development.EtaleCohomology.DivisorCycles.CycleCount
public import Development.EtaleCohomology.DivisorCycles.FinSubOf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace LateralTheory.Fin.FinSub
theorem finite_subrepresentation_etale_charpoly_instance : LateralTheory.DivDb.FinSub := by
  apply LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinSub := finite_subrepresentation_etale_charpoly_instance
end LateralTheory.Fin.FinSub
