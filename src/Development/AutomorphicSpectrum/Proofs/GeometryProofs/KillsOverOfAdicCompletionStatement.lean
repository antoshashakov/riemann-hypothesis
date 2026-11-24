module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.killsOver_of_adic_completion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S), (∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b)) → KillsOver u Y b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KillsAdic.killsOver_of_forall_pow | exact GlobalTheory.CompanionTheory.Ar.KillsAdic.killsOver_of_forall_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.KillsAdic.killsOver_of_forall_pow <;> assumption)
