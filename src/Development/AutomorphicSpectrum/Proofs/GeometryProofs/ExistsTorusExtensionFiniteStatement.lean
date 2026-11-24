module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusExtensionFinite
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_torus_extension_finite : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre | exact GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre <;> assumption)
