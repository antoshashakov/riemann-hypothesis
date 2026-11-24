module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PredualVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.predual_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (L : Lat ξ (Module.Dual Ω Li)) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li) [FiniteDimensional Ω V], (L.map V.dualRestrict).IsVBOn T r ⊤ → (L.predualIn V).IsVBOn T r V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.predualIn_isVBOn | exact GlobalTheory.CompanionTheory.Ar.Lat.predualIn_isVBOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.predualIn_isVBOn <;> assumption)
