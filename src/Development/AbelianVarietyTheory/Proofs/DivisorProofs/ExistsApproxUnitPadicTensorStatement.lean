module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxUnitPadicTensor
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_approx_unit_padic_tensor : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), ∃ (b : E) (s : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] s ∧ (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = (z : ℚ_[ℓ] ⊗[ℚ] E) * (1 + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) * s) := by
  first | (exact @GlobalTheory.PadicTensorApprox.exists_approx_unit) | (exact GlobalTheory.PadicTensorApprox.exists_approx_unit) | (intros; apply GlobalTheory.PadicTensorApprox.exists_approx_unit  <;> assumption)
