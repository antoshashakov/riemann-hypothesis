module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_existsUnique_semilinear : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (spMap c ≫ x) E'), ∃! j : E →ₛₗ[c] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts | exact GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts | (intros; apply GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts <;> assumption)
