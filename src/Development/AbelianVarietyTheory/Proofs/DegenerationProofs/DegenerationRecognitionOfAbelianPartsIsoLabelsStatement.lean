module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationRecognitionOfAbelianPartsIsoLabels
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.degenerationRecognition_of_abelianPartsIsoLabels : UrCSt → URecSt := by
  first | exact @GlobalTheory.Ex.Recognition.urec_of_abelian | exact GlobalTheory.Ex.Recognition.urec_of_abelian | (intros; apply GlobalTheory.Ex.Recognition.urec_of_abelian <;> assumption)
