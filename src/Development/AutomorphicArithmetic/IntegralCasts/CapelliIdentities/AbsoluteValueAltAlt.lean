module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfiniteNormOneElements
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs : ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
    {t : E | t * σ t = 1}.Infinite :=
  UpperTheory.infinite_norm_one_elements
