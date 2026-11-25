module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.ModEq
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RaCarry
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem frobeniusChain_carry : ∀ (p f : ℕ), 2 ≤ p → 0 < f → ∀ (y : ℕ → NNReal), (∀ n, y (n + f) = y n) → (∀ n, y n ≤ 1) → (∀ n, y n ^ p ≤ y (n + 1)) → ∀ (e : Fin f → ℕ) (j : ℕ), 2 ≤ ∑ n, e n → (∑ n : Fin f, e n * p ^ (n : ℕ)) ≡ p ^ (j + 1) [MOD (p ^ f - 1)] → ∏ n : Fin f, y n ^ e n ≤ y j ^ p :=
  PositivityTheory.HtPt.Ra.carry

end GlobalTheory.CompanionTheory.Ar.GR
