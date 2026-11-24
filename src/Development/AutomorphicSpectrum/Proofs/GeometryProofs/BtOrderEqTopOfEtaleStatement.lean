module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtale
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_eq_top_of_etale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), Etale Γ.G.hom → Γ.btOrder ⊤ = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale | exact GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale <;> assumption)
