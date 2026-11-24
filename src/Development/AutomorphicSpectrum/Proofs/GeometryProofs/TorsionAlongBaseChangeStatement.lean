module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torsion_along_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange | exact GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange <;> assumption)
