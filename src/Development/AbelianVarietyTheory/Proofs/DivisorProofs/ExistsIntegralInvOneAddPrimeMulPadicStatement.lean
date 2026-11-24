module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvOneAddPrimeMulPadic
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] (s : S), IsIntegral ℤ_[ℓ] s → ∃ r : S, (1 + (ℓ : S) * s) * r = 1 ∧ IsIntegral ℤ_[ℓ] r := by
  first | (exact @GlobalTheory.exists_integral_inv_one_add_prime_mul) | (exact GlobalTheory.exists_integral_inv_one_add_prime_mul) | (intros; apply GlobalTheory.exists_integral_inv_one_add_prime_mul  <;> assumption)
