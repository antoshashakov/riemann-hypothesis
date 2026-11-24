module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotient
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.separated_of_finite_surjective_quotient : ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q → IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left → IsSeparated Y.hom := by
  first | exact @GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | exact GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | (intros; apply GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective <;> assumption)
