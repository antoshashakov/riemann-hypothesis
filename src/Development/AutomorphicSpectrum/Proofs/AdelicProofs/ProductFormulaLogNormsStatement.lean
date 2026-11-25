module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNorms
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.product_formula_log_norms : ∀ (k : Type) [Field k] [NumberField k] (x : k), x ≠ 0 → {p | (LogNorms.ofElt x).finSum p ≠ 0}.Finite ∧ (∑ s : k →+* ℂ, Real.log ‖s x‖) + ∑ᶠ p, (LogNorms.ofElt x).finSum p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings | exact GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings <;> assumption)
