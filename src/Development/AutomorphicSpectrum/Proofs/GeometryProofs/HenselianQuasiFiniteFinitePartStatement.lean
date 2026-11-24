module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem _root_.GlobalTheory.T.henselian_quasi_finite_finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian | exact GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian <;> assumption)
