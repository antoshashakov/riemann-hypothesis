module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentFormsIntermediateField
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.linearIndependent_forms_intermediate_field : ∀ (Ks L0 L WL : Type) [Field Ks] [Field L0] [Field L] [Algebra Ks L0] [Algebra L0 L] [Algebra Ks L]
    [IsScalarTower Ks L0 L] [AddCommGroup WL] [Module L WL] [Module Ks WL] [IsScalarTower Ks L WL]
    (WK : Submodule Ks WL) (n : ℕ) (bs : Fin n → WL), (∀ a, bs a ∈ WK) → Submodule.span Ks (Set.range bs) = WK →
    LinearIndependent L bs → ∀ (ι : L0 ⊗[Ks] WK →ₗ[Ks] WL), (∀ (c : L0) (f : WK), ι (c ⊗ₜ[Ks] f) = algebraMap L0 L c • (f : WL)) →
    ∀ (m : ℕ) (x : Fin m → L0 ⊗[Ks] WK), LinearIndependent L0 x → LinearIndependent L (fun a => ι (x a)) := by
  first | exact @GlobalTheory.ksForm_tensor_linearIndependent | exact GlobalTheory.ksForm_tensor_linearIndependent | (intros; apply GlobalTheory.ksForm_tensor_linearIndependent <;> assumption)
