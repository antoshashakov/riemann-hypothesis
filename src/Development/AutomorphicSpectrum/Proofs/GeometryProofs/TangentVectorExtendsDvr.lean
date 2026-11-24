module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.WeilBound.CoreStatements.AmpleLineBundles.TangentVectorExtendsOverIntegers
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_lifts_of_local : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (dualMap c) ≫ w.left) → ∃ e, (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) :=
  @CoverDenseAlt.tangent_vector_extends_over_integers

end GlobalTheory.CompanionTheory.Ar
