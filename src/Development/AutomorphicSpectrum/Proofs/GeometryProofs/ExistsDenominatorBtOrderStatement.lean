module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorBtOrder
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_denominator_btOrder :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
      (Γ : GlobalTheory.CompanionTheory.Ar.BT.QFGroup R T),
      ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ :=
  @GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank
