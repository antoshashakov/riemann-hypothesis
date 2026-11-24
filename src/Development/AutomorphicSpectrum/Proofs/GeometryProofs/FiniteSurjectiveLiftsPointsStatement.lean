module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveLiftsPoints
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.finite_surjective_lifts_points : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_lift_algClosure | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_lift_algClosure | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_lift_algClosure <;> assumption)
