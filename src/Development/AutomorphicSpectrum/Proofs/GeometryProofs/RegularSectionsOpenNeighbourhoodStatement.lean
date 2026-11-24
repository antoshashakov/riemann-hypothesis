module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularSectionsOpenNeighbourhood
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.regular_sections_open_neighbourhood : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li),
    IsCptGen ξ → SmoothOfRelativeDimension g G.hom →
    ∀ (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li),
      (∀ j, S j ∈ M.lat p) → (∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) →
      ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
        (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near <;> assumption)
