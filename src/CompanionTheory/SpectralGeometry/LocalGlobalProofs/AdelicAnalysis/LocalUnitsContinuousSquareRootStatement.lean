module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalUnitsContinuousSquareRoot
import Supplements.MathlibImports.AnalysisAndTactics
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.local_units_continuous_square_root : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ, ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧ (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit <;> assumption)
