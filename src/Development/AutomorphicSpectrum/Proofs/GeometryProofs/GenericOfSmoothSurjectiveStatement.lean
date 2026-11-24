module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

theorem _root_.GlobalTheory.T.generic_of_smooth_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀) (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ → Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | exact GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective <;> assumption)
