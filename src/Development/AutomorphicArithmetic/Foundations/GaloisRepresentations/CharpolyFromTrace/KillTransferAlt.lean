module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

section Weil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end Weil

def KillTransfer : Prop :=
  ∀ (I V V' : Type) [Group I] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (ρ : Representation ℂ I V) (ρ' : Representation ℂ I V'), (Set.range ρ).Finite →
    (∀ s, LinearMap.trace ℂ V (ρ s) = LinearMap.trace ℂ V' (ρ' s)) →
    ∀ x : MonoidAlgebra ℂ I, ρ'.asAlgebraHom x = 0 → ρ.asAlgebraHom x = 0

end UpperTheory.Gal.NearKilling
