module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.SupIndep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedMemOfOrbitHeight
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.invariant_mem_of_orbit_height_separation : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by
  first | exact @GlobalTheory.fixed_mem_of_orbit_height | exact GlobalTheory.fixed_mem_of_orbit_height | (intros; apply GlobalTheory.fixed_mem_of_orbit_height <;> assumption)
