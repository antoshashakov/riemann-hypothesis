module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointLiftAlongIso
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.generic_point_lift_along_iso : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W), IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) → ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen <;> assumption)
