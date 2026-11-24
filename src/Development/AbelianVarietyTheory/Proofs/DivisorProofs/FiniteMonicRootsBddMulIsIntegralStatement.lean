module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegral
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral : ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  first | (exact @GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_roots_bdd_mul_isIntegral <;> assumption)
