module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.GermVanishesOfGenericVanishing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem germ_vanish_of_generic_dominated : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 :=
  PositivityTheory.UnitarySelfGeneration.germ_vanishes_of_generic_vanishing

end GlobalTheory.CompanionTheory.Ggeo
