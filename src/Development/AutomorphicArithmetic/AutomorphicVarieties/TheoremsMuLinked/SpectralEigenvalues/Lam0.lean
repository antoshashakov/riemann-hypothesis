module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Lam0
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.lam0 :
    ∀ (O B M : Type) [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [AddCommGroup M] [Module B M] [Module.Finite B M] (x : B →ₐ[O] O), Module.annihilator B M ≤ RingHom.ker x → ∃ (lam : M →+ O) (m₀ : M), (∀ (a : B) m, lam (a • m) = x a * lam m) ∧ lam m₀ ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qf1.lam0
