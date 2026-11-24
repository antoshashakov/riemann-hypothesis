module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByPowPrimePowModEq
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy : ∀ (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X] (x : G) (p k : ℕ), p.Prime → Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  first | exact @GlobalTheory.card_fixedBy_pow_prime_pow_modEq | exact GlobalTheory.card_fixedBy_pow_prime_pow_modEq | (intros; apply GlobalTheory.card_fixedBy_pow_prime_pow_modEq <;> assumption)
