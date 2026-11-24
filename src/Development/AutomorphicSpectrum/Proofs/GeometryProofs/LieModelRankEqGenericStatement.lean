module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_rank_eq_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq | exact GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq <;> assumption)
