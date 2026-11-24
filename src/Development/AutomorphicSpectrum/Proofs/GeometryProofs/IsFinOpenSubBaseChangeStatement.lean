module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.isFinOpenSub_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ'.IsFinOpenSub (F ⁻¹ᵁ U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange | exact GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange <;> assumption)
