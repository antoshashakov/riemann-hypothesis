module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreTwistEqUnionEmbeddings
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.fibre_twist_eq_union_embeddings : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ), p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q → fibre (twist p Q) Ψ y = embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪ embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist <;> assumption)
