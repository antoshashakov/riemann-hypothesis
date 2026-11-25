module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.semistable_model_ring_isDomain : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → IsDomain (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) := by
  first | exact @GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C | exact GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C | (intros; apply GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C <;> assumption)
