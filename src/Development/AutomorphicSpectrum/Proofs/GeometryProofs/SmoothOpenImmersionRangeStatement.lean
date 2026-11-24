module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothOpenImmersionRange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.smooth_open_immersion_range : ∀ (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ), SmoothOfRelativeDimension n (j ≫ g) → SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | exact GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp <;> assumption)
