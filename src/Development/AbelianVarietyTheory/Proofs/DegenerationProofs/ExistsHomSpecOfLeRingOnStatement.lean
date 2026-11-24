module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomSpecOfLeRingOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_hom_spec_of_le_ringOn' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  first | exact @GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn | exact GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn | (intros; apply GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn <;> assumption)
