module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonNonzeroOfPolynomialOnRealLines
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (ι : Type) [Finite ι] (f : ι → V → ℂ), (∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ)) → (∀ i, ∃ v, f i v ≠ 0) → ∃ v, ∀ i, f i v ≠ 0 := by
  first | exact @GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | exact GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | (intros; apply GlobalTheory.exists_common_nonzero_of_polynomial_on_lines <;> assumption)
