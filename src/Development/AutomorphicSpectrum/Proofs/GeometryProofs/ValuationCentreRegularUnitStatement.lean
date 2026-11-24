module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCentreRegularUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.valuation_centre_regular_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper <;> assumption)
