module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfProdFunEq
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq : ∀ {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : (∀ l, V l) →ₘₗ[ℂ] ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l),
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) = a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  exact @GlobalTheory.multilinear_sum_eq_of_prod_fun_eq
