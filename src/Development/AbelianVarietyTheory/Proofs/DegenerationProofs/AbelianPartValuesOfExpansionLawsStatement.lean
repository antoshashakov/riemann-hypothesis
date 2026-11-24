module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLaws
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.abelianPartValues_of_expansionLaws : Laws → BrUthSt := by
  first | exact @GlobalTheory.ThetaInValues.brUth_of_laws | exact GlobalTheory.ThetaInValues.brUth_of_laws | (intros; apply GlobalTheory.ThetaInValues.brUth_of_laws <;> assumption)
