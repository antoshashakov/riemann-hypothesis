module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF :
    {A : Type} → [inst : Ring A] → [Algebra ℂ A] → (ℂ → A) → Prop :=
  fun {A} _ _ f => ∃ p : Polynomial A, ∀ Y : ℂ, f Y = Polynomial.eval (algebraMap ℂ A Y) p
