module

public import GroundTheory.LocalFields.LocalFourier
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalFieldSelfdualMeasureExists
import Supplements.MathlibImports.AnalysisAndTactics
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.local_field_selfdual_measure_exists : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (ψ : AddChar K Circle), Continuous ψ → ψ ≠ 1 → SelfDual (GroundTheory.LocalField.selfDualMeasure ψ) (fun s t => ((ψ (s * t) : Circle) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure | exact GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure <;> assumption)
