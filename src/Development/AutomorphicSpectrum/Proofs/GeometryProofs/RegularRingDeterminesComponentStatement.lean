module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.regular_ring_determines_component : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie <;> assumption)
