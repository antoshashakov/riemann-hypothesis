module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.val_at_complex_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (a : Ω) (u : L),
    ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a u → ValAt ξ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) a (σ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex | exact GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex <;> assumption)
