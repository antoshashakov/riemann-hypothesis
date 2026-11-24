module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ForallTermNeZeroOfPsiRelation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.forall_term_ne_zero_of_psiRelation : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiRel D (𝟙_ _) f → (∃ α j, (f α).f j ≠ 0) → ∀ α, ∃ j, (f α).f j ≠ 0 := by
  first | exact @GlobalTheory.forall_ne_zero_of_psiRel | exact GlobalTheory.forall_ne_zero_of_psiRel | (intros; apply GlobalTheory.forall_ne_zero_of_psiRel <;> assumption)
