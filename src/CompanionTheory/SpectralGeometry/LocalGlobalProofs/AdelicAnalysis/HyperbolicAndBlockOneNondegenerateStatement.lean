module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerate
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.hyperbolic_and_block_one_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypJ J) ∧ ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND | exact GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND | (intros; apply GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND <;> assumption)
