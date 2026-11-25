module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquare
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ := by
  first | exact @GlobalTheory.QNorm.exists_isQuad | exact GlobalTheory.QNorm.exists_isQuad | (intros; apply GlobalTheory.QNorm.exists_isQuad <;> assumption)
