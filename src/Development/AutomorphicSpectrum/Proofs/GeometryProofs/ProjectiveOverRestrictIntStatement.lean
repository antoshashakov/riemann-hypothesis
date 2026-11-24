module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverRestrictInt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.projective_over_restrict_int : ∀ (o : Type) [CommRing o] [Module.Finite ℤ o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → IsProjOver (s ≫ spMap (Int.castRingHom o)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int | exact GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int <;> assumption)
