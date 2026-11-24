module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.NNReal.Defs
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProductInequalitiesForceEquality
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped Matrix TensorProduct
open Matrix

theorem _root_.GlobalTheory.T.product_inequalities_force_equality : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.grcount | exact GlobalTheory.CompanionTheory.Ar.GR.grcount | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.grcount <;> assumption)
