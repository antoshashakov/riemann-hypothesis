module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsFiniteTypeOverIntegers
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.coords_finite_type_over_integers : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int <;> assumption)
