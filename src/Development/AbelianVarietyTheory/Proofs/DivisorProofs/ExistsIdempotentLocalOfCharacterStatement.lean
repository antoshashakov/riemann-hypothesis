module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLocalOfCharacter
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct
universe u

theorem _root_.GlobalTheory.T.exists_idempotent_local_of_character : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧ ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  first | (exact @GlobalTheory.exists_idem_local_of_character) | (exact GlobalTheory.exists_idem_local_of_character) | (intros; apply GlobalTheory.exists_idem_local_of_character <;> assumption)
