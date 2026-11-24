module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamily
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family : ∀ (F : Type) [Field F] (I : Type) (k : I → Type) [∀ i, Field (k i)] (f : ∀ i, F →+* k i), ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (g : ∀ i, k i →+* L) (h : F →+* L), ∀ i, (g i).comp (f i) = h := by
  first | (exact @GlobalTheory.exists_isAlgClosed_embeddings_of_family) | (exact GlobalTheory.exists_isAlgClosed_embeddings_of_family) | (intros; apply GlobalTheory.exists_isAlgClosed_embeddings_of_family  <;> assumption)
