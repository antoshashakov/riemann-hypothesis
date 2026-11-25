module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.units_open_embedding_local_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
  first | exact @GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding | exact GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding | (intros; apply GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding <;> assumption)
