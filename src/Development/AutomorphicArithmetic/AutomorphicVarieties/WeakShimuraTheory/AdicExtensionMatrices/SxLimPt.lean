module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SxLimPt
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxLimPt :
    ∀ {Λ A R S : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] [CommRing R] [Algebra Λ R] (I : Ideal R) [IsAdicComplete I R] (e : S → A) (y : S → R), (∀ N : ℕ, ∃ f : A →ₐ[Λ] R ⧸ I ^ (N + 1), ∀ s, f (e s) = Ideal.Quotient.mk _ (y s)) → (∀ (N : ℕ) (f f' : A →ₐ[Λ] R ⧸ I ^ (N + 1)), (∀ s, f (e s) = f' (e s)) → f = f') → ∃ f : A →ₐ[Λ] R, ∀ s, f (e s) = y s :=
  _root_.UpperTheory.Reformulated.B.Qg4.sxLimPt
