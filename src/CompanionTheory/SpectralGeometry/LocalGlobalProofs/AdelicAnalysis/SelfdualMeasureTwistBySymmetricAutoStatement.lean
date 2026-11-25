module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTwistBySymmetricAuto
import Supplements.MathlibImports.AnalysisAndTactics
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.selfdual_measure_twist_by_symmetric_auto : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ (B : V ≃ₜ+ V), (∀ x y, χ x (B y) = χ (B x) y) → ∀ c : ℝ≥0, μ.map B = c • μ → SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => χ x (B y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist | exact GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist | (intros; apply GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist <;> assumption)
