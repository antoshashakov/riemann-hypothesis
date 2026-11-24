module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfSumMulEmbeddingsEqZero
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' : ∀ (F Ω L : Type) [Field F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ) (e : Fin m → Ω), LinearIndependent F e → (∀ t, IsAlgebraic F (e t)) → ∀ a : Fin m → L, (∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) → a = 0 := by
  first | exact @GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero | exact GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero | (intros; apply GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero <;> assumption)
