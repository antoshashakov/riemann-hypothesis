module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Development.EtaleCohomology.DivisorCycles.SpecLiePf
public import Development.EtaleCohomology.DivisorCycles.SpecPtPf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace LateralTheory.Fin.SpecLie
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_spectrum_lie_algebra_instance : LateralTheory.DivDb.SpecLie := by
  apply LateralTheory.DivDb.SpecLiePf.SpecLie_of <;> first | exact etale_special_point_exists_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.SpecLie := etale_spectrum_lie_algebra_instance
end LateralTheory.Fin.SpecLie
