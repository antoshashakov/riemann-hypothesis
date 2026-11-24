module

public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicPointOverNumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg


theorem _root_.GlobalTheory.T.algebraic_point_over_number_field : ∀ (C : Type) [Field C] [CharZero C] [Algebra.IsAlgebraic ℚ C] (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : Sp C ⟶ X), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (e : K →+* C) (x' : Sp K ⟶ X), spMap e ≫ x' = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend.exists_numberField_point | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend.exists_numberField_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend.exists_numberField_point <;> assumption)
