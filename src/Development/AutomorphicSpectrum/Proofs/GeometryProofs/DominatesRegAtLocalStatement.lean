module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesRegAtLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.dominates_regAt_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.dominates_localRings | exact GlobalTheory.CompanionTheory.Ar.dominates_localRings | (intros; apply GlobalTheory.CompanionTheory.Ar.dominates_localRings <;> assumption)
