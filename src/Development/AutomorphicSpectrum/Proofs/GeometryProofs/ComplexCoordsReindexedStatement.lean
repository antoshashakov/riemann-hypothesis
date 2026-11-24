module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.complex_coords_reindexed : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (K' : Type) (J' : K' → Type) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, J' k) → ℂ), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → IsCptGen ξ' → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → CoordsAt ξ' y' z w → CoordsAt ξ y (z ≫ g) (fun p : (Σ k, J k) => w ⟨bk p.1, bx p.1 p.2⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down | exact GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down <;> assumption)
