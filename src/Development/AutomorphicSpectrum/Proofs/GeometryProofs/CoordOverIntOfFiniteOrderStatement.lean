module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.coord_over_int_of_finite_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] [Module.Finite ℤ o] (κ : Type) [Finite κ] (x : κ → Ω), CoordTie o ξ x → ∃ (N : ℕ) (x' : Fin (N + 1) → Ω), CoordTie ℤ ξ x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite | exact GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite <;> assumption)
