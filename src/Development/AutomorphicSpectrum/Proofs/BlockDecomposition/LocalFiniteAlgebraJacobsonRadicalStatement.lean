module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFiniteAlgebraJacobsonRadical
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_finite_algebra_jacobson_radical : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Module.Finite O R], Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ (⊥ : Ideal R).jacobson ∧ ∃ N : ℕ, (⊥ : Ideal R).jacobson ^ N ≤ Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) := by
  first | exact @GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le | exact GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le | (intros; apply GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le <;> assumption)
