module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChange
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.sum_embeddings_base_change : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq | exact GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq <;> assumption)
