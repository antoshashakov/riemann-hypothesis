module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubicalBundleRelAmpleOfAmpleFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A], IsAdicComplete (IsLocalRing.maximalIdeal A) A → ∀ (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ M : CP B, (∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), RelAmple ((Over.pullback x).obj B) (M.L.L.pull (pullback.fst B.hom x))) → RelAmple B M.L.L := by
  first | exact @GlobalTheory.CubicalFibreAmple.relAmple_of_fibres | exact GlobalTheory.CubicalFibreAmple.relAmple_of_fibres | (intros; apply GlobalTheory.CubicalFibreAmple.relAmple_of_fibres <;> assumption)
