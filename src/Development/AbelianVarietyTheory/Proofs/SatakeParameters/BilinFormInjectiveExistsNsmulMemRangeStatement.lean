module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRange
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Injective EF → ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  first | (exact @GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (exact GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (intros; apply GlobalTheory.bilinForm_injective_exists_mul_mem_range  <;> assumption)
