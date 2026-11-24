module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherian
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.regAt_noetherian_model_noetherian : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), CoordTie o ξ x → (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie <;> assumption)
