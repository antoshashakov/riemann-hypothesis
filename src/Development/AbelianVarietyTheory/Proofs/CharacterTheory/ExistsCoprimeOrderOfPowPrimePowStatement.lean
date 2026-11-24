module

public import Mathlib.GroupTheory.OrderOfElement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCoprimeOrderOfPowPrimePow
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  first | exact @GlobalTheory.exists_coprime_orderOf_pow_prime_pow | exact GlobalTheory.exists_coprime_orderOf_pow_prime_pow | (intros; apply GlobalTheory.exists_coprime_orderOf_pow_prime_pow <;> assumption)
