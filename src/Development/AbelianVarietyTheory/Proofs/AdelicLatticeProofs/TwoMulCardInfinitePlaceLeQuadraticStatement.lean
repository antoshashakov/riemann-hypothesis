module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardInfinitePlaceLeQuadratic
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → 2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  first | exact @GlobalTheory.QNorm.two_mul_card_infinitePlace_le | exact GlobalTheory.QNorm.two_mul_card_infinitePlace_le | (intros; apply GlobalTheory.QNorm.two_mul_card_infinitePlace_le <;> assumption)
