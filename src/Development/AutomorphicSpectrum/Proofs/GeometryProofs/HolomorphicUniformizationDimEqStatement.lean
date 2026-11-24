module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDimEq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.holomorphic_uniformization_dim_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g d : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension d A.hom → g = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension | exact GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension | (intros; apply GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension <;> assumption)
