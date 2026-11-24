module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_denominator_regular : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left), ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.RegDenom.exists_denom_regularAt
