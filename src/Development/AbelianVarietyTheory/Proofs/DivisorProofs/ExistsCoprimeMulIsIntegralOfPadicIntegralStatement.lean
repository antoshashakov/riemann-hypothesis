module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegral
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  first | (exact @GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (exact GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (intros; apply GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul  <;> assumption)
