module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficient
import Supplements.MathlibImports.AnalysisAndTactics
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.contDiffOn_chart_globalWhittakerCoefficient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open | exact GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open | (intros; apply GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open <;> assumption)
