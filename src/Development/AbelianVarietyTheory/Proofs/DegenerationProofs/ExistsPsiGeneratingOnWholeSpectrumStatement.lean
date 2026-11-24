module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPsiGeneratingOnWholeSpectrum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_psi_generating_on_whole_spectrum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ ψ h, Nonempty (PsiOn (setPsi D ψ h) ⊤) := by
  first | exact @GlobalTheory.PsiTop.exists_setPsi_psiOn_top | exact GlobalTheory.PsiTop.exists_setPsi_psiOn_top | (intros; apply GlobalTheory.PsiTop.exists_setPsi_psiOn_top <;> assumption)
