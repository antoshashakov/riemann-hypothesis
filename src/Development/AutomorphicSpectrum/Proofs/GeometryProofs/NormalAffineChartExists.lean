module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MkChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.CompanionTheory.Relay.normal_affine_chart_exists : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ q : Cpt ξ, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω), IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsOpenImmersion x ∧ q.1 ∈ Set.range x ∧ (∀ y ∈ Set.range x, genPt ξ ⤳ y) ∧ spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ := by
  first | exact @PositivityTheory.HtPt.Mk.ht_lat_chart | exact PositivityTheory.HtPt.Mk.ht_lat_chart
