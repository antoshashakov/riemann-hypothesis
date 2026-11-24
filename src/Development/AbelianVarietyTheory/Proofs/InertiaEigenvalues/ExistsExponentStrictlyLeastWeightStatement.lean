module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExponentStrictlyLeastWeight
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_least_weight_exponent : ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ, (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) → ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  first | exact @GlobalTheory.exists_exponent_strictly_least_weight | exact GlobalTheory.exists_exponent_strictly_least_weight | (intros; apply GlobalTheory.exists_exponent_strictly_least_weight <;> assumption)
