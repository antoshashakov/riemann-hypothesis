module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplex
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.char_zero_centre_of_complex : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z), IsCptGen ξ → Char0 ξ ⟨centre z, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.char_zero_centre_complex_point | exact GlobalTheory.CompanionTheory.Ar.SncBase.char_zero_centre_complex_point | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.char_zero_centre_complex_point <;> assumption)
