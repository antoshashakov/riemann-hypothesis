module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_stalk_fraction_of_generic : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ b c : X.presheaf.stalk p.1, genMap ξ p c ≠ 0 ∧ a * genMap ξ p c = genMap ξ p b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_frac_genMap | exact GlobalTheory.CompanionTheory.Ar.exists_frac_genMap | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_frac_genMap <;> assumption)
