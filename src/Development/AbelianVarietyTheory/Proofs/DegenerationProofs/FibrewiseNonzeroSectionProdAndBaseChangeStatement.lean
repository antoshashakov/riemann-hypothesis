module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.fibrewiseNonzeroSection_prod_and_baseChange : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), (ThetaNZ G U.P.L.L → ∃ σ : U.SecGT (𝟙_ _) 1, FibNZ (𝟙_ _ ⊗ G).hom σ) ∧ ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') → FibNZ (𝟙_ _ ⊗ G).hom σ → FibNZ (𝟙_ _ ⊗ G').hom σ' := by
  first | exact @GlobalTheory.fibNZ_prod_and_baseChange | exact GlobalTheory.fibNZ_prod_and_baseChange | (intros; apply GlobalTheory.fibNZ_prod_and_baseChange <;> assumption)
