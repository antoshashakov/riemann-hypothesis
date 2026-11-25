module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ExistsExtensionEmbeddingAlgClosed
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.exists_extension_embedding_alg_closed : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A), ∃ j' : k' →+* A, j'.comp f = j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField <;> assumption)
