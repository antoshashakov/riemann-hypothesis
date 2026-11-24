module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffwiseDerivationMvPowerSeries
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.exists_coeffwise_derivation_mvPowerSeries : ∀ (σ R : Type) [CommRing R] (D : Derivation ℤ R R), ∃ E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R), ∀ F α, MvPowerSeries.coeff α (E F) = D (MvPowerSeries.coeff α F) := by
  first | exact @GlobalTheory.mvPowerSeries_derivation_coeffwise | exact GlobalTheory.mvPowerSeries_derivation_coeffwise | (intros; apply GlobalTheory.mvPowerSeries_derivation_coeffwise <;> assumption)
