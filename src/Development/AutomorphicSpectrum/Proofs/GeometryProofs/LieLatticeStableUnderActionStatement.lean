module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_lattice_stable_under_action : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω V), M.IsActOf act.act ρ → ∀ (p : Cpt ξ) (a : O), ∀ e ∈ M.lat p, ρ a e ∈ M.lat p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable | exact GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable <;> assumption)
