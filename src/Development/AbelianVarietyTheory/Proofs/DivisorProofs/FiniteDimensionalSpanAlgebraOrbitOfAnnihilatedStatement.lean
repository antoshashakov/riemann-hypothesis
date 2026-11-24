module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤ ∏ t ∈ T, (p t).natDegree := by
  first | exact @GlobalTheory.killed_span_adjoin_finrank_le | exact GlobalTheory.killed_span_adjoin_finrank_le | (intros; apply GlobalTheory.killed_span_adjoin_finrank_le <;> assumption)
