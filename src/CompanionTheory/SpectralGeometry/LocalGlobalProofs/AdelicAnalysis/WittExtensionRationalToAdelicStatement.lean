module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelic
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.witt_extension_rational_to_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 → gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) → ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.TransA.trans_adelic | exact GlobalTheory.CompanionTheory.SW.TransA.trans_adelic | (intros; apply GlobalTheory.CompanionTheory.SW.TransA.trans_adelic <;> assumption)
