module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLocalInverseOfInjOn
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)


theorem _root_.GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn : ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W → DifferentiableOn ℂ g W → Set.InjOn g W → ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  first | exact @GlobalTheory.InjHol.exists_local_inverse_of_injOn | exact GlobalTheory.InjHol.exists_local_inverse_of_injOn | (intros; apply GlobalTheory.InjHol.exists_local_inverse_of_injOn <;> assumption)
