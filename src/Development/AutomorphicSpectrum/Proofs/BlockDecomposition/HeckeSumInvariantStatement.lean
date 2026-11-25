module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariant
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.hecke_sum_invariant : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite → (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) → ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  first | exact @GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | exact GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | (intros; apply GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed <;> assumption)
